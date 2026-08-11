import Std.Http
import Std.Http.Server
import Std.Async
import Std.Net
import TrustServer.Store
import TrustServer.Config
import TrustServer.Http
import TrustServer.Routes
import TrustServer.Auth
import TrustServer.Federation.Routes

/-!
# The node

The routes, in one list, and the socket they answer on.

Three paths are claimed twice, and which copy wins is a decision rather than an
accident.  `TrustServer.Routes` has a local-only `GET /api/certificates`, an
export, and a descriptor; `TrustServer.Federation.Routes` has the same three
with §7's delegation, §4.1's peers and §2's real counts.  The federating ones
supersede, so they go first — and the superseded three are dropped by name
rather than left to be shadowed, because a route that can never match is a route
somebody will later change and wonder why nothing happened.
-/

open Std Std.Http Std.Async Std.Net

namespace TrustServer

/-- The three `TrustServer.Routes` entries that `Federation.Routes` supersedes. -/
def supersededByFederation : Array (Method × String) :=
  #[(.get, "/api/certificates"), (.get, "/api/certificates/export"), (.get, "/api/federation")]

/--
Everything this node answers.

Order is first-match, so the federating routes come before the local ones they
replace.  Sessions come last: none of their paths collide, and reading them at
the end matches how they are reached — a person signs in, having already found
the node.
-/
def allRoutes : Array Route :=
  Federation.federationRoutes
    ++ Federation.peerRoutes
    ++ Routes.certificateRoutes.filter (fun r =>
         !supersededByFederation.any (fun (m, p) => r.method == m && r.path == p))
    ++ Auth.sessionRoutes

/--
Bind, and hand back the running node.

The handler reads the `App` out of a ref on every request rather than closing
over it, because a node has to know its own externally reachable URL — §5.2
checks an announcement against it and §7.1 puts it in `via` — and when the
configured port is `0` that is not known until the socket is bound.
-/
def serve (config : ServerConfig) (app : IO.Ref App) (loopbackOnly : Bool := true) :
    Async Server := do
  let addr := SocketAddress.v4 {
    addr := if loopbackOnly then IPv4Addr.ofParts 127 0 0 1 else IPv4Addr.ofParts 0 0 0 0
    port := UInt16.ofNat config.port }
  Server.serve addr
    ({ onRequest := fun req => do (router (← app.get) allRoutes).onRequest req } :
      Server.StatelessHandler)
    config.httpConfig

/-- The port the node ended up on, which is only interesting when `port` was 0. -/
def boundPort (server : Server) : Nat :=
  match server.localAddr with
  | some (.v4 a) => a.port.toNat
  | some (.v6 a) => a.port.toNat
  | none => 0

/--
Start a node: open the store, admit the seeds, learn our own address, serve.

A seed is the operator's own decision, so it is queried from the start (§5.1)
rather than waiting to be promoted the way a peer somebody else announced does.
-/
def start (config : ServerConfig) : IO Unit := do
  let loopbackOnly := !config.bindAll
  let store ← Store.open config.storeDir config.storeOptions
  let (certificates, peers) ← store.counts
  IO.println s!"store {config.storeDir}: {certificates} certificates, {peers} peers queried"
  for seed in config.seeds do
    let _ ← store.putPeer { url := seed, status := .seed }
  Async.block do
    let app ← IO.mkRef ({ config, store } : App)
    let server ← serve config app loopbackOnly
    let port := boundPort server
    -- Now that the port is known, say what our own URL is, so that §5.2 can
    -- refuse an announcement naming anything else and §7.1 can put it in `via`.
    -- A configured `PUBLIC_URL` always wins: behind a proxy the node's own port
    -- is not what anybody reaches it by.
    if config.publicUrl.isEmpty then
      app.modify fun a =>
        { a with config := { a.config with publicUrl := s!"http://127.0.0.1:{port}" } }
    IO.println s!"listening on http://127.0.0.1:{port}"
    IO.println s!"{allRoutes.size} routes, {if config.localMode then "local mode" else "public"}"
    server.waitShutdown

end TrustServer
