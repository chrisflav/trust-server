import Std.Http
import Std.Http.Server
import Std.Async
import Lean
import Trust.Cert
import Trust.Net
import Trust.Pgp
import TrustServer.Http

/-!
# Identity: sessions, tokens and keys

Who is publishing, and how this node came to believe it.

## Sessions are rows, not signatures

The TypeScript keeps a session in a cookie signed with an HMAC: the cookie
carries the identity, and the MAC is what stops a client editing it.  That is a
reasonable design in a runtime with SHA-2 in its standard library.  Lean v4.32.0
has none — there is no SHA-256 anywhere in the toolchain — and the way out is
not to hand-roll one.

So a session here is a **row in the store**: `freshToken` produces 32 bytes from
the OS, the cookie carries nothing but that value, and the server looks it up.
Nothing needs signing, because nothing in the cookie is a statement — it is a
name for a row, and the row is the statement.  A database made the cryptography
unnecessary rather than the other way round, which is a better place to end up
than a hand-written MAC would have been.

The one thing this costs is stated where it is paid: `Store.Session` explains
that the value is stored as it stands, because there is no digest to store
instead.

Three kinds of credential go through the same table, because all three are the
same thing — an opaque value with an owner and a lifetime — and only their
lifetimes differ: a browser session, a command-line token, and the anti-forgery
`state` of an OAuth round trip.

## What a token can and cannot do

A token says *who is publishing*.  It cannot forge a signature, so it is not
what makes a certificate worth anything: an `attested` row is this server's word
about its own authentication (§3.1) and never leaves the node.

## Local mode

§9: one identity, no OAuth, no public surface.  A local database has one user —
the person running it — and asking them to sign in to their own laptop, through
a GitHub app they would have to register first, would be ceremony rather than
security.
-/

open Std Std.Http Std.Async Std.Net
open Lean (Json ToJson FromJson toJson fromJson?)

namespace TrustServer

namespace Auth

/-! ## Percent-encoding

`Std.Http` keeps a URI's parts encoded, which is the right default for a node
that relays them, so a route that actually *reads* a value decodes it here.
Written out rather than taken from `Std.Http.URI`, whose query encoder leaves
`&` and `=` alone — exactly the two characters that must not survive being put
into a query string. -/

/-- The unreserved set of RFC 3986; everything else is escaped. -/
private def unreserved (c : UInt8) : Bool :=
  (0x41 ≤ c && c ≤ 0x5a) || (0x61 ≤ c && c ≤ 0x7a) || (0x30 ≤ c && c ≤ 0x39) ||
    c == 0x2d || c == 0x2e || c == 0x5f || c == 0x7e

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (0x30 + n.toNat) else Char.ofNat (0x41 + (n.toNat - 10))

/-- Percent-encode a value for a query string or a path segment. -/
def percentEncode (s : String) : String := Id.run do
  let mut out := ""
  for byte in s.toUTF8.toList do
    if unreserved byte then out := out.push (Char.ofNat byte.toNat)
    else out := out ++ "%" |>.push (hexDigit (byte >>> 4)) |>.push (hexDigit (byte &&& 0x0f))
  return out

private def hexValue? (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - 0x30))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (c.toNat - 0x61 + 10))
  else if 'A' ≤ c && c ≤ 'F' then some (UInt8.ofNat (c.toNat - 0x41 + 10))
  else none

/--
Undo percent-encoding.

`plusIsSpace` is not a style choice: `+` means a space in
`application/x-www-form-urlencoded`, which is what `URLSearchParams` produces
and therefore what arrives in a query string, and it means a literal `+` in a
path segment.  Decoding both the same way would silently corrupt one of them.

A `%` that does not introduce two hex digits is left alone rather than treated
as an error: this decodes attacker-supplied input, and the useful behaviour for
a login containing a stray `%` is to fail to match a row rather than to fail the
request.
-/
def percentDecode (s : String) (plusIsSpace : Bool := false) : String := Id.run do
  let mut out : ByteArray := .empty
  let mut rest := s.toList
  while true do
    match rest with
    | [] => break
    | '%' :: a :: b :: tail =>
      match hexValue? a, hexValue? b with
      | some hi, some lo => out := out.push ((hi <<< 4) ||| lo); rest := tail
      | _, _ => out := out ++ "%".toUTF8; rest := a :: b :: tail
    | '+' :: tail =>
      out := out ++ (if plusIsSpace then " " else "+").toUTF8
      rest := tail
    | c :: tail => out := out ++ (String.singleton c).toUTF8; rest := tail
  return String.fromUTF8! out

/-- A query parameter, decoded, which is how a route wants it. -/
def query (req : Request Body.Stream) (name : String) : Option String :=
  (queryParam req name).map (percentDecode · (plusIsSpace := true))

/--
The tail of a path, after a prefix route's `path`.

Decoded, because a login or a fingerprint is a value rather than a route.
-/
def pathTail (req : Request Body.Stream) (prefix_ : String) : String :=
  percentDecode ((requestPath req).drop prefix_.length).toString

/-! ## Time -/

/-- Epoch milliseconds as RFC 3339, which is what a listing shows. -/
def isoOfMs (ms : Nat) : String :=
  if ms == 0 then "" else
    Trust.rfc3339Format.format (Std.Time.DateTime.ofTimestampWithZone
      (Std.Time.Timestamp.ofMillisecondsSinceUnixEpoch (Std.Time.Millisecond.Offset.ofNat ms))
      .UTC)

/-! ## The cookie -/

/-- The name the frontend already sends; changing it would sign everybody out. -/
def sessionCookie : String := "trust_session"

/-- Thirty days, as the TypeScript has it. -/
def sessionLifetimeMs : Nat := 30 * 24 * 60 * 60 * 1000

/-- Ten minutes: long enough for a person to finish signing in, short enough to forget. -/
def stateLifetimeMs : Nat := 10 * 60 * 1000

private def cookieAttributes (config : ServerConfig) : String :=
  let secure := if config.cookieSecure then "; Secure" else ""
  s!"; Path=/; HttpOnly; SameSite=Lax{secure}"

/-- The `Set-Cookie` that starts a session. -/
def setSessionCookie (config : ServerConfig) (token : String) : String :=
  s!"{sessionCookie}={token}{cookieAttributes config}; Max-Age={sessionLifetimeMs / 1000}"

/-- The `Set-Cookie` that ends one.  Same attributes, or the browser keeps the old one. -/
def clearSessionCookie (config : ServerConfig) : String :=
  s!"{sessionCookie}={cookieAttributes config}; Max-Age=0"

/-! ## Credentials -/

/--
Resolve a presented value to the row it names.

The hash-map probe finds a candidate; `secureEqual` is what accepts it.  That
ordering is deliberate: a lookup by key is not a comparison anyone can time, and
the decision is still made by a comparison that cannot be.
-/
def credential (app : App) (token : String) (kind : SessionKind) : IO (Option Session) := do
  if token.isEmpty then return none
  let some session ← app.store.getSession token | return none
  if session.kind != kind then return none
  if !secureEqual token session.token then return none
  let now ← nowMs
  if !session.alive now then
    -- A dead credential is swept as it is presented, so that an abandoned OAuth
    -- round trip does not leave a row behind forever.
    app.store.deleteSession session.token
    return none
  return some session

/-- The single identity a local database has (§9). -/
def ensureLocalIdentity (app : App) : IO Identity := do
  let login := if app.config.name.isEmpty then "local" else app.config.name
  match ← app.store.getIdentity login with
  | some identity => return identity
  | none =>
    -- A negative GitHub id can never collide with a real one.
    let identity : Identity := { login, githubId := -1 }
    app.store.putIdentity identity
    return (← app.store.getIdentity login).getD identity

/--
Who is making this request, if anybody.

A browser session, a command-line token, or — in local mode — the fact that
there is only one person this database could mean.  The CLI cannot hold a cookie
session, and pushing somebody through a browser to publish something they just
signed on their own machine would make signing the awkward path rather than the
normal one.
-/
def signedIn (app : App) (req : Request Body.Stream) : IO (Option Identity) := do
  let byToken ← match bearerToken req with
    | some token => credential app token .api
    | none => pure none
  match byToken with
  | some session =>
    -- Only tokens record a last use.  A browser session would append a row per
    -- request, which is a lot of log for a column nobody decides anything from.
    app.store.putSession { session with lastUsedMs := ← nowMs }
    return ← app.store.getIdentity session.login
  | none =>
    let bySession ← match cookie req sessionCookie with
      | some raw => credential app raw .browser
      | none => pure none
    match bySession with
    | some session => return ← app.store.getIdentity session.login
    | none => if app.config.localMode then return some (← ensureLocalIdentity app) else return none

/-- Run a handler as a signed-in identity, or refuse. -/
def withIdentity (app : App) (req : Request Body.Stream)
    (k : Identity → ContextAsync (Response Body.Any)) : ContextAsync (Response Body.Any) := do
  match ← signedIn app req with
  | some identity => k identity
  | none => fail Response.unauthorized "sign in with GitHub, or send a Bearer token"

/-! ## GitHub

Two outbound calls, both through `Trust.Net`, because Lean has no HTTPS client
of its own and the core library already owns the one this project uses. -/

/-- §8's limits, as they apply to a call this node makes. -/
def outboundPolicy (config : ServerConfig) : Trust.Net.Policy :=
  { maxResponseBytes := config.policy.maxResponseBytes, timeoutMs := config.policy.peerTimeoutMs }

/-- What GitHub says an account is.  Only the login is ever used as an identity. -/
structure GitHubAccount where
  id : Int := -1
  login : String
  avatarUrl : String := ""
  deriving Inhabited, Repr

/-- Where a sign-in starts, with a fresh anti-forgery `state` recorded here. -/
def authorizeUrl (app : App) : IO String := do
  -- Abandoned round trips are swept here, where one is being started: a state
  -- nobody came back with is a row that would otherwise sit in the log forever.
  let _ ← app.store.expireSessions
  let state ← freshToken
  let now ← nowMs
  app.store.putSession {
    token := state, id := ← freshToken, kind := .oauthState,
    expiresMs := now + stateLifetimeMs }
  let redirect := s!"{app.config.publicUrl}/auth/github/callback"
  return "https://github.com/login/oauth/authorize?" ++ String.intercalate "&" [
    s!"client_id={percentEncode app.config.github.clientId}",
    s!"redirect_uri={percentEncode redirect}",
    "scope=read%3Auser",
    s!"state={percentEncode state}"]

/-- Spend a `state` exactly once.  A second attempt with the same one is a replay. -/
def consumeState (app : App) (state : String) : IO Bool := do
  match ← credential app state .oauthState with
  | none => return false
  | some session =>
    app.store.deleteSession session.token
    return true

/--
What GitHub said, when what it said was no.

The token endpoint refuses with `error` and `error_description` in the body and
HTTP 200 in the status line, so the body is the only thing separating "that
secret is wrong" from "that code was already spent" — and this used to discard
it, leaving an operator with a message that named nothing they could act on.

Nothing in a *refusal* is secret: the client secret travels in the request,
never in the reply, and `error` with `error_description` is the whole of what
GitHub says when it says no.

A body that is not JSON is described and never quoted, and that restraint is
load-bearing rather than fastidious.  The reply this cannot parse is most often
a **successful** exchange in `application/x-www-form-urlencoded`, whose first
field is the access token — so a message that echoed the body would write a live
credential into the log, and into whatever the browser is shown.  The shape is
what an operator needs, and the shape is sayable without the contents.
-/
private def githubComplaint (response : Trust.Net.Response) : String :=
  match (Json.parse response.body).toOption with
  | some json =>
    let field (name : String) : Option String := (json.getObjValAs? String name).toOption
    match field "error", field "error_description" with
    | some e, some description => s!": {e} — {description}"
    | some e, none => s!": {e}"
    | none, _ => s!" (HTTP {response.status}, and no error in the JSON either)"
  | none =>
    if response.body.startsWith "access_token=" || response.body.startsWith "error=" then
      s!" (HTTP {response.status}: it answered form-encoded rather than JSON, which is what " ++
        "GitHub does when the request does not ask for JSON.  A `trust` older than " ++
        "chrisflav/trust#21 does not ask, so this node is built against one.)"
    else
      s!" (HTTP {response.status}: the {response.body.length} bytes it answered are not JSON)"

/--
Exchange the code for a token, and ask GitHub who it belongs to.

The second call goes to the GraphQL endpoint rather than to `GET /user`, and the
reason is a limitation rather than a preference: `Trust.Net.getUrl` sends no
`Authorization` header and `Trust.Net.get` sets only `Accept`, so the only way
to make an authenticated call with the core library as it stands is a POST —
which GraphQL accepts and the REST user endpoint does not.  The core library is
a pinned dependency this package must not fork, and `viewer` under `read:user`
answers exactly the same question.
-/
def exchangeCode (app : App) (code : String) : IO (Except String GitHubAccount) := do
  let policy := outboundPolicy app.config
  let body := Json.compress <| Json.mkObj [
    ("client_id", Json.str app.config.github.clientId),
    ("client_secret", Json.str app.config.github.clientSecret),
    ("code", Json.str code),
    ("redirect_uri", Json.str s!"{app.config.publicUrl}/auth/github/callback")]
  match ← Trust.Net.postJson "https://github.com/login/oauth/access_token" "" body policy with
  | .error e => return .error s!"GitHub did not answer: {e}"
  | .ok response =>
    let some token := (Json.parse response.body).toOption.bind
      (·.getObjValAs? String "access_token" |>.toOption) |
      return .error s!"GitHub did not return a token{githubComplaint response}"
    let queryBody := Json.compress <| Json.mkObj [
      ("query", Json.str "query { viewer { databaseId login avatarUrl } }")]
    match ← Trust.Net.postJson "https://api.github.com/graphql" token queryBody policy with
    | .error e => return .error s!"GitHub user lookup failed: {e}"
    | .ok userResponse =>
      match Json.parse userResponse.body >>= (·.getObjVal? "data") >>= (·.getObjVal? "viewer") with
      | .error e => return .error s!"GitHub user lookup failed: {e}"
      | .ok viewer =>
        match viewer.getObjValAs? String "login" with
        | .error _ => return .error "GitHub named no account"
        | .ok login => return .ok {
            login
            id := (viewer.getObjValAs? Int "databaseId").toOption.getD (-1)
            avatarUrl := (viewer.getObjValAs? String "avatarUrl").toOption.getD "" }

/--
The keys GitHub itself publishes for an account.

Used to mark a key `github` rather than `self`: it ties a fingerprint to an
account through a party that is not us, which is a materially stronger claim
than "somebody pasted this here while signed in".  Unauthenticated, so
`getUrl` is all it needs, and a failure means `self` rather than an error —
GitHub being unreachable is not a reason to refuse somebody their own key.
-/
def githubPublicKeys (app : App) (login : String) : IO (Array String) := do
  if app.config.localMode then return #[]
  let url := s!"https://api.github.com/users/{percentEncode login}/gpg_keys"
  match ← Trust.Net.getUrl url (outboundPolicy app.config) with
  | .error _ => return #[]
  | .ok response =>
    match Json.parse response.body with
    | .error _ => return #[]
    | .ok body =>
      match body.getArr? with
      | .error _ => return #[]
      | .ok rows => return rows.filterMap fun row =>
          match row.getObjValAs? String "raw_key" with
          | .ok raw => if raw.isEmpty then none else some raw
          | .error _ => none

/-- Whitespace is not part of an armoured key, so it is not part of the comparison. -/
private def squashed (s : String) : String :=
  String.ofList (s.toList.filter fun c => !(c == ' ' || c == '\n' || c == '\r' || c == '\t'))

/-! ## Identity as JSON -/

/--
An identity, as `/api/me` and a trust list report one.

There is no numeric `id` here, which the TypeScript has: the login *is* the key
these logs are filed under, and inventing a row number to hand out beside it
would be a second identifier to keep consistent.  The frontend reads `login`.
-/
def identityJson (identity : Identity) : Json :=
  Json.mkObj [("login", Json.str identity.login), ("avatarUrl", Json.str identity.avatarUrl)]

/-! ## The routes -/

/--
A redirect that still carries a JSON body.

Every response this server makes is JSON (`TrustServer.Http`), and a browser
following a 302 never looks at the body — but a client that is *not* a browser,
which is most of what talks to a node, gets something it can read rather than
nothing.
-/
private def redirectTo (url : String) (setCookie : Option String) :
    ContextAsync (Response Body.Any) := do
  let builder := Response.withStatus .found |>.header! "Location" url
  let builder := match setCookie with
    | some value => builder.header! "Set-Cookie" value
    | none => builder
  json builder (Json.mkObj [("ok", Json.bool true), ("location", Json.str url)])

/-- `GET /auth/github`: start the round trip. -/
private def githubStart (app : App) (_req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  if app.config.localMode then
    return ← fail Response.notFound "this node is local; there is nobody to sign in as"
  if app.config.github.clientId.isEmpty then
    return ← fail Response.serviceUnavailable "this node has no GitHub app configured"
  redirectTo (← authorizeUrl app) none

/-- `GET /auth/github/callback`: finish it, or say plainly which half failed. -/
private def githubCallback (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  if app.config.localMode then
    return ← fail Response.notFound "this node is local; there is nobody to sign in as"
  let some code := query req "code" | return ← badRequest "bad OAuth state"
  let some state := query req "state" | return ← badRequest "bad OAuth state"
  if !(← consumeState app state) then
    return ← badRequest "bad OAuth state"
  match ← exchangeCode app code with
  | .error why => fail (Response.withStatus .badGateway) why
  | .ok account =>
    -- The same account under a new name is the same account: its rows move with
    -- it rather than the person losing their keys to a rename.
    match ← app.store.identityByGitHubId account.id with
    | some existing => app.store.renameIdentity existing.login account.login
    | none => pure ()
    app.store.putIdentity {
      login := account.login, githubId := account.id, avatarUrl := account.avatarUrl }
    let token ← freshToken
    let now ← nowMs
    app.store.putSession {
      token, id := ← freshToken, kind := .browser, login := account.login,
      expiresMs := now + sessionLifetimeMs }
    let destination := if app.config.appUrl.isEmpty then "/" else app.config.appUrl
    redirectTo destination (some (setSessionCookie app.config token))

/-- `GET /api/me`. -/
private def me (app : App) (req : Request Body.Stream) : ContextAsync (Response Body.Any) := do
  match ← signedIn app req with
  | some identity =>
    -- Local mode says so, because "signed out" would send the frontend looking
    -- for an OAuth flow that does not exist here.
    let fields := [("user", identityJson identity)] ++
      (if app.config.localMode then [("local", Json.bool true)] else [])
    json Response.ok (Json.mkObj fields)
  | none => json Response.ok (Json.mkObj [("user", Json.null)])

/-- `POST /auth/logout`: forget the row, then the cookie. -/
private def logout (app : App) (req : Request Body.Stream) : ContextAsync (Response Body.Any) := do
  match cookie req sessionCookie with
  | some raw =>
    match ← credential app raw .browser with
    | some session => app.store.deleteSession session.token
    | none => pure ()
  | none => pure ()
  json (Response.ok.header! "Set-Cookie" (clearSessionCookie app.config))
    (Json.mkObj [("ok", Json.bool true)])

private def tokenJson (session : Session) : Json :=
  Json.mkObj [
    ("id", Json.str session.id), ("name", Json.str session.name),
    ("createdAt", Json.str (isoOfMs session.createdMs)),
    ("lastUsedAt", Json.str (isoOfMs session.lastUsedMs))]

/-- `POST /api/tokens`: mint one for the command line. -/
private def issueToken (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  withIdentity app req fun identity => do
    let name := match ← bodyJson app req with
      | .ok body => ((body.getObjValAs? String "name").toOption.getD "").take 100 |>.toString
      | .error _ => ""
    let token := "trust_" ++ (← freshToken)
    app.store.putSession { token, id := ← freshToken, kind := .api, login := identity.login, name }
    -- The TypeScript says "it is not stored and cannot be shown again", which is
    -- true of a digest and would be a lie here: there is no SHA-2 to hash it
    -- with, so it *is* stored.  It is still never shown again.
    json Response.ok (Json.mkObj [
      ("token", Json.str token),
      ("note", Json.str "copy this now; it is not shown again")])

/-- `GET /api/tokens`: what exists, never what it is. -/
private def listTokens (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  withIdentity app req fun identity => do
    let sessions ← app.store.listSessions identity.login .api
    json Response.ok (Json.mkObj [("tokens", Json.arr (sessions.map tokenJson))])

/-- `DELETE /api/tokens/:id`. -/
private def revokeToken (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  withIdentity app req fun identity => do
    let id := pathTail req "/api/tokens/"
    match ← app.store.sessionById id with
    | some session =>
      -- Somebody else's token is not this account's to revoke, and answering
      -- "no such token" rather than "not yours" says nothing about whose it is.
      if session.login == identity.login then app.store.deleteSession session.token
    | none => pure ()
    json Response.ok (Json.mkObj [("ok", Json.bool true)])

/--
`POST /api/keys`: register a public key.

The public half only.  Anything carrying a private key block is refused rather
than stored: a server that never holds signing material cannot leak it, and
signing belongs on the machine that holds the key.  The refusal is made here, on
the text, before anything is asked to parse it — so it does not depend on the
verifier being present, and so somebody who pasted the wrong half is told what
they actually did.
-/
private def registerKey (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  withIdentity app req fun identity => do
    let .ok body ← bodyJson app req | return ← badRequest "expected a JSON body"
    let .ok armored := body.getObjValAs? String "armored" |
      return ← badRequest "expected an armored PGP public key"
    if (armored.splitOn "PRIVATE KEY BLOCK").length > 1 then
      return ← badRequest "that is a private key — never send one here"
    if (armored.splitOn "BEGIN PGP PUBLIC KEY BLOCK").length ≤ 1 then
      return ← badRequest "expected an armored PGP public key"
    match ← app.verifier.fingerprint armored with
    | .error why => badRequest why
    | .ok fingerprint =>
      let published ← githubPublicKeys app identity.login
      let onGitHub := published.any fun candidate => squashed candidate == squashed armored
      let verifiedVia := if onGitHub then "github" else "self"
      app.store.putKey { fingerprint, login := identity.login, armored, verifiedVia }
      json Response.ok (Json.mkObj [
        ("fingerprint", Json.str fingerprint), ("verifiedVia", Json.str verifiedVia)])

private def keyJson (key : PublicKey) : Json :=
  Json.mkObj [
    ("fingerprint", Json.str key.fingerprint), ("armored", Json.str key.armored),
    ("verifiedVia", Json.str key.verifiedVia)]

/-- `GET /api/keys/:login`. -/
private def keysOfLogin (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let login := pathTail req "/api/keys/"
  let keys ← app.store.keysForLogin login
  json Response.ok (Json.mkObj [("keys", Json.arr (keys.map keyJson))])

/--
`GET /api/key/:fingerprint`.

Federated entries are attributed to a key rather than to a name, so a reader
checking one needs to be able to ask for it that way.
-/
private def keyOfFingerprint (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let fingerprint := pathTail req "/api/key/"
  match ← app.store.keyByFingerprint fingerprint with
  | none => fail Response.notFound "no key here with that fingerprint"
  | some key =>
    json Response.ok (Json.mkObj [
      ("fingerprint", Json.str key.fingerprint), ("armored", Json.str key.armored),
      ("login", Json.str key.login), ("verifiedVia", Json.str key.verifiedVia)])

/--
Everything identity: the OAuth round trip, the session it produces, the tokens
the command line uses instead, and the keys an account puts its name to.
-/
def sessionRoutes : Array Route := #[
  { method := .get, path := "/auth/github", run := githubStart },
  { method := .get, path := "/auth/github/callback", run := githubCallback },
  { method := .get, path := "/api/me", run := me },
  { method := .post, path := "/auth/logout", run := logout },
  { method := .post, path := "/api/tokens", run := issueToken },
  { method := .get, path := "/api/tokens", run := listTokens },
  { method := .delete, path := "/api/tokens/", run := revokeToken },
  { method := .post, path := "/api/keys", run := registerKey },
  { method := .get, path := "/api/keys/", run := keysOfLogin },
  { method := .get, path := "/api/key/", run := keyOfFingerprint }]

end Auth

end TrustServer
