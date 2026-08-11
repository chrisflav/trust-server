import Std.Http
import Std.Http.Server
import Std.Async
import Std.Net
import TrustServer.Store
import TrustServer.Config

/-!
# The server skeleton

Deliberately almost empty.  This branch is the store and the configuration; the
routes, the sessions and the federation belong to other work, and writing a
half-finished version of them here would only have to be deleted.  What is here
is the smallest thing that proves the pieces fit together: a configuration read
from the environment, a store opened on disk, and an HTTP server bound to a port
and answering.

`/api/health` is the only route, and it lives here rather than in a routing
module because there is no routing module yet.  Anything else gets a 404.
-/

open Std Std.Http Std.Async Std.Net

namespace TrustServer


/-- The path of a request, with the query string dropped. -/
def requestPath (req : Request Body.Stream) : String := toString req.line.uri.path

/-- A JSON response, since every response this server will ever make is one. -/
def jsonResponse (builder : Response.Builder) (payload : Lean.Json) :
    ContextAsync (Response Body.Any) := do
  let body ← Body.Full.ofString (Lean.Json.compress payload)
  return builder |>.header! "Content-Type" "application/json" |>.body (Body.Any.ofBody body)

/--
The skeleton handler: liveness, and nothing else yet.

The health answer reports what the store actually holds rather than a constant
`true`, so that a green health check means the log was opened and indexed and
not merely that a process is listening.
-/
def skeletonHandler (config : ServerConfig) (store : Store) : Server.StatelessHandler where
  onRequest := fun req => do
    match req.line.method, requestPath req with
    | .get, "/api/health" =>
      let (certificates, peers) ← store.counts
      jsonResponse Response.ok <| Lean.Json.mkObj [
        ("ok", Lean.Json.bool true),
        ("name", Lean.Json.str config.name),
        ("certificates", Lean.toJson certificates),
        ("peers", Lean.toJson peers)]
    | _, path =>
      jsonResponse Response.notFound <| Lean.Json.mkObj [
        ("error", Lean.Json.str "not found"), ("path", Lean.Json.str path)]

/--
Bind, and hand back the running server.

The address is taken from the configuration but the *bound* address is read back
off the server, because a port of `0` means "whichever one is free" and the test
that talks to this needs to know which one that was.
-/
def serve (config : ServerConfig) (store : Store) (loopbackOnly : Bool := true) :
    Async Server := do
  let addr := SocketAddress.v4 {
    addr := if loopbackOnly then IPv4Addr.ofParts 127 0 0 1 else IPv4Addr.ofParts 0 0 0 0
    port := UInt16.ofNat config.port }
  Server.serve addr (skeletonHandler config store) config.httpConfig

/-- The port the server ended up on, which is only interesting when `port` was 0. -/
def boundPort (server : Server) : Nat :=
  match server.localAddr with
  | some (.v4 a) => a.port.toNat
  | some (.v6 a) => a.port.toNat
  | none => 0

end TrustServer
