import Std.Async
import Std.Sync.Channel
import Std.Time
import Trust.Federation
import Trust.Net
import Trust.Time
import TrustServer.Http
import TrustServer.Federation.Client

/-!
# Federation as this node performs it

`Trust.Federation` decides what may be believed — §3.4, §6 and §7.1 live there,
and nothing here re-decides any of it.  What is here is who to ask, what to do
with the answer, and how long to wait: importing a bundle, walking a peer's
export, recording a node that announced itself, and answering a question this
node cannot answer alone.

Two things in this file are worth reading before the code.

**Blocking work never happens on the event loop.**  A signature check runs
`gpg`, a peer fetch runs `curl`, and both would sit on the thread the timers and
the sockets share.  `detached` moves them onto a thread of their own.  Without
it a node that federates with a node in the same process deadlocks, which is
exactly what the tests do — and which a deployment does too, whenever one
handler waits on another node that is waiting on this one.

**The fan-out is bounded by a clock, not by a peer count** (§7.2).  Peers are
asked concurrently and the budget is one wall-clock deadline for all of them, so
one unreachable peer costs a reader `queryBudgetMs` once rather than
`peerTimeoutMs` per peer.  What has arrived when the deadline passes is what is
returned, and the answer says it was cut short: "nobody vouches for this" and "I
could not find out" are different sentences.
-/

namespace TrustServer
namespace Federation
namespace Service

open Std Std.Async
open Lean (Json toJson fromJson?)

/-! ## Running blocking work off the loop -/

/--
Run an `IO` action on a thread of its own.

`gpg` and `curl` are subprocesses and the store is a file; none of them may
occupy the thread that the HTTP server and the budget's timer are sharing.
-/
def detached (x : IO α) : Async α := do
  let task ← (IO.asTask x Task.Priority.dedicated : BaseIO (Task (Except IO.Error α)))
  Async.ofAsyncTask task

/-! ## Rendering -/

/-- Epoch milliseconds as the timestamp everything else in this protocol is written in. -/
def rfc3339OfMs (ms : Nat) : String :=
  Trust.rfc3339Format.format <| Std.Time.DateTime.ofTimestampWithZone
    (Std.Time.Timestamp.ofMillisecondsSinceUnixEpoch (Std.Time.Millisecond.Offset.ofNat ms)) .UTC

/--
§4.4's hints, as they travel.

Rendered as their own object rather than mixed in beside the checked fields, and
carried next to `hintsVerified: false`: a receiver **must** mark them unverified,
and a shape that makes them look like the rest is how that gets forgotten.
-/
def renderHints (hints : Hints) (origin : String) : Json :=
  Json.mkObj [
    ("issuer", Json.str hints.issuer),
    ("keyVerifiedVia", Json.str hints.keyVerifiedVia),
    ("origin", Json.str (if hints.origin.isEmpty then origin else hints.origin))]

/-- §3.3's entry: the four checkable fields, and the hints beside them. -/
def renderEntry (cert : StoredCertificate) (origin : String) : Json :=
  Json.mkObj [
    ("claim", toJson cert.entry.claim),
    ("signature", Json.str cert.entry.signature),
    ("key", Json.str cert.entry.key),
    ("fingerprint", Json.str cert.entry.fingerprint),
    ("hints", renderHints cert.hints origin)]

/-- §4's bundle. -/
def renderBundle (origin : String) (entries : Array StoredCertificate)
    (revocations : Array Trust.SignedRevocation) (cursor : String) (complete : Bool) : Json :=
  Json.mkObj [
    ("protocol", Json.str Trust.Federation.protocolVersion),
    ("origin", Json.str origin),
    ("entries", Json.arr (entries.map (renderEntry · origin))),
    ("revocations", Json.arr (revocations.map toJson)),
    ("cursor", Json.str cursor),
    ("complete", Json.bool complete)]

/-! ## The node's own description (§2) -/

/-- The host part of a URL, for a node that never gave itself a name. -/
private def hostOf (url : String) : String :=
  match Trust.Net.parseUrl url with
  | .ok (_, host, _, _) => host
  | .error _ => "trust"

/-- This node's normalised URL, and `""` when it does not know one. -/
def ourUrl (app : App) : String :=
  match Trust.Net.normalizeUrl app.config.publicUrl with
  | .ok url => url
  | .error _ => ""

/-- §2's descriptor.  `counts` is read from the store rather than remembered. -/
def descriptorFor (app : App) : IO Trust.Federation.Descriptor := do
  let (certificates, peers) ← app.store.counts
  let url := ourUrl app
  return {
    url
    name := if app.config.name.isEmpty then hostOf url else app.config.name
    software := "trust-server/0.1.0"
    policy := {
      maxDepth := app.config.policy.maxDepth
      maxEntries := app.config.policy.maxEntries
      autodiscover := app.config.policy.autodiscover }
    certificates, peers }

/-! ## Export (§4.1) -/

private def laterCursor (a b : String) : String :=
  match Cursor.decode? a, Cursor.decode? b with
  | some x, some y => if y.after x then b else a
  | none, some _ => b
  | _, _ => a

private def earlierCursor (a b : String) : String :=
  match Cursor.decode? a, Cursor.decode? b with
  | some x, some y => if y.after x then a else b
  | none, some _ => a
  | _, _ => b

/--
A page of this node's log, in cursor order (§4.1).

Certificates and revocations are separate tables walked from one cursor, so the
bundle may only say it has delivered as far as the *lesser* of the two when
either was cut short.  Advancing to the greater would leave rows of the other
table behind the cursor and never send them, which is the failure §4's `complete`
exists to prevent, one table down.
-/
def exportBundle (app : App) (since : String) (limit : Nat) : IO Json := do
  let limit := max 1 (min limit app.config.policy.maxEntries)
  let certificates ← app.store.certificatesSince since limit
  let revocations ← app.store.revocationsSince since limit
  let cursor :=
    if certificates.truncated && revocations.truncated then
      earlierCursor certificates.cursor revocations.cursor
    else if certificates.truncated then certificates.cursor
    else if revocations.truncated then revocations.cursor
    else laterCursor certificates.cursor revocations.cursor
  -- §4: `complete` is set honestly, because a receiver that mistakes truncation
  -- for exhaustion silently stops syncing.
  let complete := !certificates.truncated && !revocations.truncated
  return renderBundle (ourUrl app) certificates.values revocations.values cursor complete

/-! ## Import (§4.2) -/

/--
Keep what survives §3.4 and §6, and say what did not.

The decisions are `Trust.Federation.checkBundle`'s; this stores the survivors and
records where they came from.  A bad entry costs only itself: a peer that sends
one forgery among a hundred honest entries has sent ninety-nine honest entries,
and dropping the lot would let anyone deny service to a node by poisoning
somebody else's export.
-/
def importBundle (app : App) (arriving : Client.Arriving) (fromPeer : String) :
    IO Trust.Federation.ImportReport := do
  let (report, entries, revocations) ←
    Trust.Federation.checkBundle arriving.bundle app.verifier
  let now ← nowMs
  for entry in entries do
    let key := certificateKey entry.fingerprint entry.claim.hash entry.claim.hasher
    let hints := (arriving.hints.get? key).getD { origin := arriving.bundle.origin }
    -- §3.5's collision is the store's to resolve; it keeps the later `asserted`.
    let _ ← app.store.putCertificate { entry, hints, fromPeer, fetchedMs := now }
  for revocation in revocations do
    -- §6 rule 4: kept even when the certificate it names has never been seen.
    let _ ← app.store.putRevocation revocation
  if arriving.unreadable == 0 then
    return report
  return { report with
    rejected := report.rejected + arriving.unreadable
    reasons := report.reasons.push
      s!"{arriving.unreadable} entries were not §3.3 entries, or carried no signature (§3.1)" }

/-! ## Pulling (§4.1 → §4.2) -/

/-- What one peer's catch-up came to. -/
structure PullReport where
  peer : String
  ok : Bool := true
  accepted : Nat := 0
  rejected : Nat := 0
  revocations : Nat := 0
  /-- How many bundles it took; a truncating peer needs more than one. -/
  rounds : Nat := 0
  cursor : String := ""
  error : String := ""
  deriving Inhabited, Repr

def PullReport.toJson (r : PullReport) : Json :=
  Json.mkObj [
    ("peer", Json.str r.peer), ("ok", Json.bool r.ok),
    ("accepted", Lean.toJson r.accepted), ("rejected", Lean.toJson r.rejected),
    ("revocations", Lean.toJson r.revocations), ("rounds", Lean.toJson r.rounds),
    ("cursor", Json.str r.cursor), ("error", Json.str r.error)]

/--
Catch up with one peer, following its cursor until it says it is complete.

`complete: false` means *resume from `cursor`*, not stop — a receiver that
mistook truncation for exhaustion would silently stop syncing at whatever the
sender's `maxEntries` happens to be.  Bounded by `rounds` as well as by the
peer's honesty: a node that always answers `complete: false` with the same
cursor would otherwise be an infinite loop, and it costs nothing to assume
somebody will eventually be that node.
-/
def pullFrom (app : App) (peerUrl : String) (rounds : Nat := 20) : IO PullReport := do
  let peer ← app.store.getPeer peerUrl
  let mut cursor := (peer.map (·.cursor)).getD ""
  let mut report : PullReport := { peer := peerUrl, cursor }
  for _ in [0:rounds] do
    match ← Client.fetchBundle peerUrl cursor app.config.policy with
    | .error why =>
      app.store.notePeerSeen peerUrl cursor why
      return { report with ok := false, error := why, cursor }
    | .ok arriving =>
      let imported ← importBundle app arriving peerUrl
      report := { report with
        accepted := report.accepted + imported.accepted
        rejected := report.rejected + imported.rejected
        revocations := report.revocations + imported.revocations
        rounds := report.rounds + 1 }
      let next := arriving.bundle.cursor
      -- No forward progress means there is nothing more to have, whatever the
      -- peer says about completeness.
      if next.isEmpty || next == cursor then
        break
      cursor := next
      app.store.notePeerSeen peerUrl cursor ""
      if arriving.bundle.complete then
        break
  app.store.notePeerSeen peerUrl cursor ""
  return { report with cursor }

/-- Catch up with everyone worth asking (§5.1), one at a time to stay polite. -/
def pullFromAll (app : App) : IO (Array PullReport) := do
  let peers ← app.store.queriedPeers
  let mut reports := #[]
  for peer in peers do
    reports := reports.push (← pullFrom app peer.url)
  return reports

/-! ## Discovery (§5.2) -/

structure AnnounceResult where
  url : String
  name : String
  status : PeerStatus
  deriving Inhabited

/--
Record a node that has announced itself.

The descriptor is fetched and its `url` must equal what was announced, after
normalisation.  That single check is what stops this endpoint being a scanner:
only a host that actually runs a node, and knows its own name, can be announced
through it, so an announcement cannot direct this node's traffic at an arbitrary
third party.  It is not optional, and neither is the normalisation — string
equality fails on a trailing slash and would turn the check into a formality.

Discovery proposes; only the operator promotes.  `autodiscover` is the operator
saying in advance that they are content to be proposed to, and it defaults to
off (§5.1).
-/
def announce (app : App) (announced : String) : IO (Except String AnnounceResult) := do
  match Trust.Net.normalizeUrl announced with
  | .error why => return .error why
  | .ok url =>
    -- `blocked` is absorbing, and a blocked node is not one to send a request to
    -- in order to find that out.
    if let some existing ← app.store.getPeer url then
      if existing.status == .blocked then
        return .error "that node is blocked here"
    match ← Client.fetchDescriptor url app.config.policy with
    | .error why => return .error why
    | .ok descriptor =>
      let claimed := (Trust.Net.normalizeUrl descriptor.url).toOption.getD ""
      if claimed != url then
        return .error "that node calls itself something else; refusing to record it"
      let status ← app.store.discoverPeer url descriptor.name app.config.policy.autodiscover
      return .ok { url, name := descriptor.name, status }

/-! ## Delegated query (§7) -/

/-- §7's question, as this node was asked it. -/
structure Question where
  hash : String := ""
  hasher : String := ""
  fingerprint : String := ""
  /-- How many further hops the request may travel; `0` is local only. -/
  depth : Nat := 0
  /-- §7.1's chain: the URLs already in it. -/
  via : Array String := #[]
  deriving Inhabited, Repr

/-- Whether a question names anything to look up at all. -/
def Question.isEmpty (q : Question) : Bool := q.hash.isEmpty && q.fingerprint.isEmpty

/-- §7.4's answer. -/
structure Answer where
  certificates : Array StoredCertificate := #[]
  /-- §7.2: set when the budget expired with peers still out, or a peer failed. -/
  truncated : Bool := false
  askedPeers : Nat := 0
  deriving Inhabited

/--
Whether this node is already in the chain (§7.1).

Asked of `mayRelayTo` rather than by comparing URLs again: we are in `via`
exactly when `via` forbids relaying to us, and the length bound is taken out of
the way so that only the membership rule answers.  Two implementations of "is
this URL in the chain" is one more than a protocol with a loop rule should have.
-/
def inChain (via : Array String) (url : String) : Bool :=
  !Trust.Federation.mayRelayTo via url (maxViaLength := via.size + 1)

/-- Everything stored that answers the question, with §6.2 already applied. -/
def matching (app : App) (question : Question) : IO (Array StoredCertificate) := do
  let hasher := if question.hasher.isEmpty then none else some question.hasher
  let found ←
    if !question.hash.isEmpty then
      app.store.certificatesByHash question.hash hasher
    else if !question.fingerprint.isEmpty then
      app.store.certificatesByFingerprint question.fingerprint
    else
      pure #[]
  let wanted := question.fingerprint.toLower
  return found.filter fun cert =>
    (question.fingerprint.isEmpty || cert.entry.fingerprint.toLower == wanted)
      && (question.hash.isEmpty || cert.entry.claim.hash.toLower == question.hash.toLower)
      && (question.hasher.isEmpty || cert.entry.claim.hasher == question.hasher)

/--
§7.3: how recently a remote answer to this question arrived.

The cache is the store: an accepted remote entry is kept with the peer it came
from and the time it arrived, so freshness is a fact about rows rather than a
second copy of them that could disagree with the first.
-/
def remoteFreshness (certificates : Array StoredCertificate) : Nat :=
  certificates.foldl (init := 0) fun newest cert =>
    if cert.fromPeer.isEmpty then newest else max newest cert.fetchedMs

/-- One peer's answer to a relayed question. -/
private structure Reply where
  peer : String
  outcome : Except String Client.Arriving
  deriving Inhabited

/--
Ask every peer at once, under one deadline (§7.2).

Each peer runs on its own thread and posts its answer to a channel; the loop
selects between that channel and a timer that expires at the budget's deadline.
The timer is rebuilt from the deadline on every pass rather than reused, so the
budget is the wall clock from the first peer being asked and not a fresh
`queryBudgetMs` per reply.

The bundles are imported *after* the loop.  Checking a signature costs a `gpg`
run, and the budget is about how long a reader waits for peers, not about how
long this node takes to check what they said.
-/
private def fanOut (app : App) (question : Question) (onward : Nat) (via : Array String)
    (targets : Array Peer) : Async (Nat × Bool) := do
  if targets.isEmpty then
    return (0, false)
  let policy := app.config.policy
  let channel : Std.Channel Reply ← Std.Channel.new
  for peer in targets do
    let url := peer.url
    let ask : IO Unit := do
      let outcome ← Client.queryPeer url {
        hash := question.hash, hasher := question.hasher,
        fingerprint := question.fingerprint, depth := onward, via } policy
      -- Unbounded, so this never blocks and never loses an answer that arrived
      -- just as the budget expired.
      discard <| channel.trySend { peer := url, outcome }
    discard <| (IO.asTask ask Task.Priority.dedicated : BaseIO _)
  let deadline := (← nowMs) + policy.queryBudgetMs
  let mut replies : Array Reply := #[]
  let mut truncated := false
  while replies.size < targets.size do
    let now ← nowMs
    if now ≥ deadline then
      truncated := true
      break
    let timer ← Sleep.mk (Std.Time.Millisecond.Offset.ofNat (deadline - now))
    let arrived ← Selectable.one #[
      .case channel.recvSelector (fun reply => pure (some reply)),
      .case timer.selector (fun _ => pure none)]
    match arrived with
    | none =>
      truncated := true
      break
    | some reply => replies := replies.push reply
  for reply in replies do
    match reply.outcome with
    | .error _ =>
      -- A peer that could not answer might have had something to say, so the
      -- answer is short rather than negative.
      truncated := true
    | .ok arriving =>
      if !arriving.bundle.complete then
        truncated := true
      let _ ← detached (importBundle app arriving reply.peer)
  return (targets.size, truncated)

/--
Answer from here, from the cache, and — if `depth` allows — from peers.

The order of the checks is the order §7 puts them in.  A node that finds itself
in `via` answers locally and relays nowhere; a cache hit within `remoteTtlS`
answers without a fan-out; and the depth this node relays is its own
`maxDepth`'s business, not the asker's, which is what `relayDepth` clamps.
-/
def answer (app : App) (question : Question) : Async Answer := do
  if question.isEmpty then
    return {}
  let policy := app.config.policy
  let me := ourUrl app
  let mut askedPeers := 0
  let mut truncated := false
  -- §7.1: clamp what we were handed to our own maximum, and relay one less.
  let clamped := min question.depth policy.maxDepth
  let onward := Trust.Federation.relayDepth question.depth policy.maxDepth
  let visited := !me.isEmpty && inChain question.via me
  if clamped > 0 && !visited then
    let known ← detached (matching app question)
    let now ← nowMs
    let fresh := remoteFreshness known
    -- §7.3: a hit within the TTL answers without a fan-out.
    let stale := fresh == 0 || now - fresh > policy.remoteTtlS * 1000
    if stale then
      let peers ← detached app.store.queriedPeers
      -- §7.1: our own URL goes on before relaying, so the next hop can do the same.
      let via := if me.isEmpty then question.via else Trust.Federation.extendVia question.via me
      let targets := peers.filter fun peer =>
        Trust.Federation.mayRelayTo via peer.url policy.maxViaLength
      let (asked, short) ← fanOut app question onward via targets
      askedPeers := asked
      truncated := short
  let certificates ← detached (matching app question)
  -- Newest assertion first; every entry here is signed, since nothing else is
  -- allowed into the store this reads.
  let certificates := certificates.qsort fun a b =>
    Trust.laterThan a.entry.claim.asserted b.entry.claim.asserted
  return { certificates, truncated, askedPeers }

/--
§7.4's response.

`canonical` travels with every entry, local or remote, so that a reader never
has to reconstruct what was signed in order to check it — and `verifiedHere`
says this node applied §3.4, which is this node's word and is expected to be
repeated rather than taken.
-/
def renderAnswer (app : App) (answer : Answer) : Json :=
  let me := ourUrl app
  let render (cert : StoredCertificate) : Json :=
    let mine := cert.fromPeer.isEmpty
    Json.mkObj [
      ("claim", toJson cert.entry.claim),
      ("canonical", Json.str cert.entry.claim.canonical),
      ("signature", Json.str cert.entry.signature),
      ("key", Json.str cert.entry.key),
      ("fingerprint", Json.str cert.entry.fingerprint),
      -- §3.1: nothing else federates, and nothing else is stored by this file.
      ("assurance", Json.str "signed"),
      ("hints", renderHints cert.hints (if mine then me else "")),
      -- §4.4: a receiver must mark hints unverified, so they are marked here
      -- rather than left for a reader to remember.
      ("hintsVerified", Json.bool false),
      ("provenance", Json.mkObj [
        ("local", Json.bool mine),
        ("origin", Json.str (if cert.hints.origin.isEmpty then (if mine then me else "") else cert.hints.origin)),
        ("fromPeer", Json.str cert.fromPeer),
        ("verifiedHere", Json.bool true),
        ("fetchedAt", if cert.fetchedMs == 0 then Json.null else Json.str (rfc3339OfMs cert.fetchedMs))])]
  Json.mkObj [
    ("certificates", Json.arr (answer.certificates.map render)),
    ("truncated", Json.bool answer.truncated),
    ("askedPeers", toJson answer.askedPeers)]

/--
The same answer as a bundle, which is what a relaying peer asked for.

Revocations for the same triples travel with it (§6 rule 4): a node that
answered with certificates alone would be relaying an assertion while withholding
its withdrawal, and the receiver would have no way to learn of the second.
-/
def renderAnswerBundle (app : App) (question : Question) (answer : Answer) : IO Json := do
  let all ← app.store.revocationsSince "" 100000
  let wanted := question.fingerprint.toLower
  let revocations := all.values.filter fun signed =>
    let r := signed.revocation
    (question.hash.isEmpty || r.hash.toLower == question.hash.toLower)
      && (question.hasher.isEmpty || r.hasher == question.hasher)
      && (question.fingerprint.isEmpty || r.fingerprint.toLower == wanted)
  return renderBundle (ourUrl app) answer.certificates
    (revocations.extract 0 app.config.policy.maxEntries) ""
    -- §4's `complete`, said honestly about a fan-out that may have been cut short.
    (!answer.truncated)

end Service
end Federation
end TrustServer
