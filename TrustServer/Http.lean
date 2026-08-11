import Std.Http
import Std.Http.Server
import Std.Async
import Std.Net
import Lean
import Trust.Cert
import Trust.Federation
import TrustServer.Store
import TrustServer.Config

/-!
# The HTTP layer

A router, and the handful of things every route needs: the path, the query, the
body as JSON, and a way to say no.

It is deliberately small.  `Std.Http` already parses the request and enforces
the byte limits §8 asks for, so what is missing between it and a route is
matching a method and a path, and turning a `Json` into a response.  Anything
larger would be a framework, and a node has fourteen endpoints.
-/

open Std Std.Http Std.Async Std.Net

namespace TrustServer

/-- Everything a route is allowed to reach. -/
structure App where
  config : ServerConfig
  store : Store
  /-- How signatures get checked.  A record, so a test can hand in another one. -/
  verifier : Trust.Verifier := Trust.defaultVerifier

/-- The path of a request, with the query string dropped. -/
def requestPath (req : Request Body.Stream) : String := toString req.line.uri.path

/--
A query parameter, percent-decoded.

`Std.Http` keeps the query as encoded pairs, which is the right default — a node
that decoded eagerly would have to re-encode to relay — so decoding happens
where a value is actually read.
-/
def queryParam (req : Request Body.Stream) (name : String) : Option String :=
  let query := req.line.uri.query
  query.toArray.findSome? fun (k, v) =>
    if toString k == name then some (v.map toString |>.getD "") else none

/-- A query parameter as a number, when it is one. -/
def queryNat (req : Request Body.Stream) (name : String) : Option Nat :=
  (queryParam req name).bind (·.toNat?)

/-- A JSON response.  Every response this server makes is one. -/
def json (builder : Response.Builder) (payload : Lean.Json) :
    ContextAsync (Response Body.Any) := do
  let body ← Body.Full.ofString (Lean.Json.compress payload)
  return builder |>.header! "Content-Type" "application/json" |>.body (Body.Any.ofBody body)

/-- An error, in the one shape every client of this server already expects. -/
def fail (builder : Response.Builder) (message : String) : ContextAsync (Response Body.Any) :=
  json builder (Lean.Json.mkObj [("error", Lean.Json.str message)])

def notFound : ContextAsync (Response Body.Any) := fail Response.notFound "not found"
def badRequest (why : String) : ContextAsync (Response Body.Any) := fail Response.badRequest why
def unauthorized : ContextAsync (Response Body.Any) :=
  fail Response.unauthorized "authentication required"
def forbidden : ContextAsync (Response Body.Any) := fail Response.forbidden "not allowed"
def methodNotAllowed : ContextAsync (Response Body.Any) :=
  fail (Response.withStatus .methodNotAllowed) "unsupported method"

/--
Read a request body as JSON.

Bounded by the configured maximum rather than by trust: a peer's body is
untrusted input (§8), and the bound belongs here as well as in `Std.Http`'s
config because this is where a body is turned into something structured.
-/
def bodyJson (app : App) (req : Request Body.Stream) : ContextAsync (Except String Lean.Json) := do
  try
    let text : String ← req.body.readAll
      (maximumSize := some (UInt64.ofNat app.config.policy.maxResponseBytes))
    if text.trimAscii.toString.isEmpty then return .error "empty body"
    match Lean.Json.parse text with
    | .ok j => return .ok j
    | .error e => return .error s!"unreadable JSON: {e}"
  catch e => return .error s!"unreadable body: {e}"

/-- The bearer token on a request, if it carries one. -/
def bearerToken (req : Request Body.Stream) : Option String := do
  let header ← req.line.headers.get? (Header.Name.ofString! "authorization")
  let value := toString header
  if value.startsWith "Bearer " then some ((value.drop 7).toString.trimAscii.toString) else none

/-- A cookie by name, from the `Cookie` header. -/
def cookie (req : Request Body.Stream) (name : String) : Option String := do
  let header ← req.line.headers.get? (Header.Name.ofString! "cookie")
  let parts := (toString header).splitOn ";"
  parts.findSome? fun part =>
    let part := part.trimAscii.toString
    if part.startsWith s!"{name}=" then some ((part.drop (name.length + 1)).toString) else none

/--
Whether a request carries the operator's admin token.

§5's peer administration is the operator's decision, so the endpoints that make
it are the only ones a token gates.  An empty configured token refuses
everything rather than allowing everything, which is the safe direction for a
value that is empty by default.
-/
def isAdmin (app : App) (req : Request Body.Stream) : Bool :=
  match bearerToken req with
  | some token => !app.config.adminToken.isEmpty && token == app.config.adminToken
  | none => false

/--
Constant-time string comparison, for anything a client can guess at.

Not because a timing attack on a session token over HTTP is likely, but because
the alternative is deciding it is unlikely every time somebody adds a
comparison.
-/
def secureEqual (a b : String) : Bool := Id.run do
  let x := a.toUTF8
  let y := b.toUTF8
  if x.size != y.size then return false
  let mut diff : UInt8 := 0
  for i in [0:x.size] do
    diff := diff ||| (x[i]! ^^^ y[i]!)
  return diff == 0

/--
A random, opaque token.

Sessions are rows in the store rather than signed cookies, so nothing here needs
a MAC and therefore nothing here needs SHA-2 — which Lean does not have.  A
database made the crypto unnecessary rather than the other way round.
-/
def freshToken : IO String := do
  let bytes ← IO.getRandomBytes 32
  return bytes.toList.foldl (fun out b =>
    out ++ (if b < 16 then "0" else "") ++ String.ofList (Nat.toDigits 16 b.toNat)) ""

/-- A route: a method, a path, and what to do. -/
structure Route where
  method : Method
  /-- Matched exactly, unless it ends in `/`, which matches a prefix. -/
  path : String
  run : App → Request Body.Stream → ContextAsync (Response Body.Any)

/-- Whether a route claims this request. -/
def Route.matches (route : Route) (req : Request Body.Stream) : Bool :=
  route.method == req.line.method &&
    (if route.path.endsWith "/" then (requestPath req).startsWith route.path
     else requestPath req == route.path)

/--
The handler: the first route that claims the request, else 404 — or 405 when
the path exists under another method, which is a materially more useful answer
than "not found" to somebody who has got the verb wrong.
-/
def router (app : App) (routes : Array Route) : Server.StatelessHandler where
  onRequest := fun req => do
    match routes.find? (·.matches req) with
    | some route =>
      try
        route.run app req
      catch e =>
        -- A route that throws must not take the connection with it, and must
        -- not describe its own internals to a stranger.
        IO.eprintln s!"trust-server: {requestPath req} failed: {e}"
        fail Response.internalServerError "the node failed to answer that"
    | none =>
      let pathExists := routes.any fun r =>
        if r.path.endsWith "/" then (requestPath req).startsWith r.path
        else requestPath req == r.path
      if pathExists then methodNotAllowed else notFound

end TrustServer
