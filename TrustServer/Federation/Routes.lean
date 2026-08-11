import TrustServer.Http
import TrustServer.Federation.Service

/-!
# The federation endpoints

Four routes an operator or a stranger reaches (`peerRoutes`), and three a peer
does (`federationRoutes`): §2's descriptor, §4.1's export and §7's query.  They
are separate arrays because the second three are what makes this node a *peer*,
and a deployment that only wanted to read from others could wire the first and
not the second.

Two decisions here are protocol rather than taste.

**`GET /api/peers` lists `seed` and `active` and nothing else** (§5.3).
Publishing `candidate` or `blocked` would leak both an operator's judgements and
a list of addresses this node has been asked to probe — the second of which is
attacker-supplied, since anyone may announce one.

**`POST /api/peers/announce` is public, and the rest are the operator's.**  An
announcement is how a node is found at all, so it cannot need a token; promoting
a peer, blocking one and forcing a pull decide who this node talks to, so they
take the admin token and refuse everything when none is configured.
-/

namespace TrustServer
namespace Federation

open Std Std.Http Std.Async
open Lean (Json toJson)

/--
A query parameter, decoded.

`Std.Http` keeps the query percent-encoded, which is right — a node that decoded
eagerly would have to re-encode to relay — so decoding happens here, where a
value is read.
-/
def queryValue (req : Request Body.Stream) (name : String) : Option String :=
  (req.line.uri.query.find? name).join.bind (·.decode)

/-- §7.1's chain, as it arrives: comma-separated, and bounded by §8. -/
def parseVia (raw : String) (maxLength : Nat) : Array String :=
  let parts := (raw.splitOn ",").filterMap fun part =>
    let part := stripTrailingSlashes part.trimAscii.toString
    if part.isEmpty then none else some part
  parts.toArray.extract 0 maxLength

/-- A field of a JSON body, when the body is an object that has it as a string. -/
private def stringField (body : Json) (name : String) : String :=
  (body.getObjValAs? String name).toOption.getD ""

/-! ## What a peer asks (§2, §4.1, §7) -/

/-- §2: the node describes itself, including the limits it enforces. -/
def descriptorRoute : Route where
  method := .get
  path := "/api/federation"
  run app _ := do
    json Response.ok (toJson (← Service.descriptorFor app))

/--
§4.1: everything since a cursor.

Public and unauthenticated, because everything it returns is signed and a
signature carries the same weight to a stranger as to a friend.  The requested
limit is honoured only as far as this node's own `maxEntries`; past that the
bundle is truncated and says so.
-/
def exportRoute : Route where
  method := .get
  path := "/api/certificates/export"
  run app req := do
    let since := (queryValue req "since").getD ""
    let limit := ((queryValue req "limit").bind (·.toNat?)).getD app.config.policy.maxEntries
    json Response.ok (← Service.exportBundle app since limit)

/--
§7: who vouches for this, here and — if `depth` allows — one hop further.

`format=bundle` is what a relaying node asks for, so that whatever it gets back
is checked by exactly the rules an imported bundle is.  Anything else gets
§7.4's response, which carries `canonical` for every entry and says plainly
whether the answer was cut short.
-/
def queryRoute : Route where
  method := .get
  path := "/api/certificates"
  run app req := do
    let policy := app.config.policy
    let question : Service.Question := {
      hash := (queryValue req "hash").getD ""
      hasher := (queryValue req "hasher").getD ""
      fingerprint := (queryValue req "fingerprint").getD ""
      depth := ((queryValue req "depth").bind (·.toNat?)).getD 0
      via := parseVia ((queryValue req "via").getD "") policy.maxViaLength }
    if question.isEmpty then
      badRequest "ask for a hash or a fingerprint"
    else
      let answer ← Service.answer app question
      if queryValue req "format" == some "bundle" then
        json Response.ok (← Service.renderAnswerBundle app question answer)
      else
        json Response.ok (Service.renderAnswer app answer)

/-- What a peer needs from this node to federate with it at all. -/
def federationRoutes : Array Route := #[descriptorRoute, exportRoute, queryRoute]

/-! ## What an operator, or a stranger, asks (§5) -/

/-- §5.3: the peers this node queries itself, and only those. -/
def peersRoute : Route where
  method := .get
  path := "/api/peers"
  run app _ := do
    let peers ← app.store.queriedPeers
    json Response.ok <| Json.mkObj [("peers", Json.arr (peers.map fun peer =>
      Json.mkObj [
        ("url", Json.str peer.url), ("name", Json.str peer.name),
        ("lastSeen", if peer.lastSeenMs == 0 then Json.null
                     else Json.str (Service.rfc3339OfMs peer.lastSeenMs))]))]

/--
§5.2: a node says it exists.

Public, and bounded by the check `Service.announce` makes: the descriptor at the
announced URL has to name that same URL back.  Without it this endpoint is a
scanner that any stranger can point at any address on this node's network.
-/
def announceRoute : Route where
  method := .post
  path := "/api/peers/announce"
  run app req := do
    match ← bodyJson app req with
    | .error why => badRequest why
    | .ok body =>
      let url := stringField body "url"
      if url.isEmpty then
        badRequest "announce a url"
      else
        -- Off the event loop: this fetches the announced node's descriptor, and
        -- that node may be waiting on this one.
        match ← Service.detached (Service.announce app url) with
        | .error why => badRequest why
        | .ok result =>
          json Response.ok <| Json.mkObj [
            ("url", Json.str result.url), ("name", Json.str result.name),
            ("status", Json.str result.status.toString)]

/-- Catch up now, rather than when the timer next says so.  The operator's. -/
def pullRoute : Route where
  method := .post
  path := "/api/peers/pull"
  run app req := do
    if !isAdmin app req then unauthorized else
    let url := match ← bodyJson app req with
      | .ok body => stringField body "url"
      | .error _ => ""
    let reports ← Service.detached <|
      if url.isEmpty then Service.pullFromAll app else do return #[← Service.pullFrom app url]
    json Response.ok <| Json.mkObj [("pulled", Json.arr (reports.map (·.toJson)))]

/--
Move a peer between the states of §5.1.

The operator's judgement, and the only way into `active` or `blocked`:
discovery may proceed to `candidate` and no further unless `autodiscover` says
otherwise.
-/
def statusRoute : Route where
  method := .post
  path := "/api/peers/status/"
  run app req := do
    if !isAdmin app req then unauthorized else
    let asked := ((requestPath req).drop "/api/peers/status/".length).toString
    match PeerStatus.ofString? asked with
    | none => badRequest s!"`{asked}` is not one of seed, active, candidate, blocked"
    | some status =>
      match ← bodyJson app req with
      | .error why => badRequest why
      | .ok body =>
        let url := stringField body "url"
        if url.isEmpty then badRequest "name a peer url" else
        if ← app.store.setPeerStatus url status then
          json Response.ok <| Json.mkObj [
            ("url", Json.str url), ("status", Json.str status.toString)]
        else
          fail Response.notFound "no such peer"

/-- §5's peer administration, and the one endpoint of it a stranger may reach. -/
def peerRoutes : Array Route := #[peersRoute, announceRoute, pullRoute, statusRoute]

end Federation
end TrustServer
