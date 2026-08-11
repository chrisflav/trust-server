import LSpec
import TrustServer.Routes
import TrustServer.Federation.Routes

/-!
# Tests

Everything here runs against a real directory on disk and, for the last two
groups, real sockets.  The store's whole premise is that its state is a file, so
a test that mocked the file would be testing something else; the federation
group takes the same line about the network and stands up a second node
in-process rather than pretending to be one.

The IO happens first and the assertions are made afterwards about what it
produced, because `LSpec.TestSeq` is a pure value: a failure then reports the
state the store was actually in rather than an exception from inside a test
description.
-/

open LSpec
open Std Std.Http Std.Async Std.Net
open Lean (Json toJson)
open TrustServer

/-! ## Fixtures -/

private def armoredKey : String :=
  "-----BEGIN PGP PUBLIC KEY BLOCK-----\nmDMEZ…\n-----END PGP PUBLIC KEY BLOCK-----\n"

private def armoredSig : String :=
  "-----BEGIN PGP SIGNATURE-----\niHUEAB…\n-----END PGP SIGNATURE-----\n"

/--
A stored entry.

The note carries a quote and a newline on purpose: those are the characters that
turn one JSONL line into two if the encoding is wrong, and a store that splices
records is a store that loses them.
-/
private def certOf (fingerprint hash asserted : String)
    (hasher : String := "semantic_hash/1") (decl : String := "Foo.bar") : StoredCertificate :=
  { entry := {
      claim := {
        decl, hash, hasher
        repo := "github.com/chrisflav/trust"
        commit := "1cbfa56f28cf6cb9acdc0ff338e4d32bceee4fa3"
        toolchain := "leanprover/lean4:v4.32.0"
        asserted
        note := "he said \"fine\", then\na newline" }
      signature := armoredSig
      key := armoredKey
      fingerprint }
    hints := {
      issuer := "alice", keyVerifiedVia := "github", origin := "https://trust.example.org" } }

private def revOf (fingerprint hash revoked : String)
    (hasher : String := "semantic_hash/1") : Trust.SignedRevocation :=
  { revocation := { fingerprint, hash, hasher, reason := "key rotated", revoked }
    signature := armoredSig
    key := armoredKey
    fingerprint }

private def fpA := "a1b2c3d4e5f60718293a4b5c6d7e8f9012345678"
private def fpB := "b1b2c3d4e5f60718293a4b5c6d7e8f9012345678"
private def hash1 := "0123456789abcdef0123456789abcdef"
private def hash2 := "fedcba9876543210fedcba9876543210"

/-! ## Timestamps and cursors -/

private def timeTests : TestSeq :=
  group "timestamps and cursors" <|
    -- The parsing itself is core's, and core tests it.  What is checked here is
    -- that this node reaches for core's rules rather than growing its own: a
    -- second implementation of §3.2's timestamps is exactly the drift the
    -- rewrite exists to remove.
    test "the epoch is zero"
      (Trust.epochMillis? "1970-01-01T00:00:00Z" = some 0) <|
    test "a known instant"
      (Trust.epochMillis? "2024-05-31T21:28:37Z" = some 1717190917000) <|
    test "milliseconds are kept"
      (Trust.epochMillis? "2024-05-31T21:28:37.250Z" = some 1717190917250) <|
    test "an offset is applied"
      (Trust.epochMillis? "2024-05-31T23:28:37+02:00" = some 1717190917000) <|
    test "second and millisecond spellings of one instant compare equal"
      (Trust.epochMillis? "2024-05-31T21:28:37Z" = Trust.epochMillis? "2024-05-31T21:28:37.000Z") <|
    test "rubbish does not parse"
      (Trust.epochMillis? "yesterday" = none) <|
    test "later is strict"
      (Trust.laterThan "2024-01-02T00:00:00Z" "2024-01-01T00:00:00Z" = true) <|
    test "a tie is not later"
      (Trust.laterThan "2024-01-01T00:00:00Z" "2024-01-01T00:00:00Z" = false) <|
    test "a cursor round trips"
      (Cursor.decode? (Cursor.encode { ms := 1717171717, seq := 4821 })
        = some { ms := 1717171717, seq := 4821 }) <|
    test "the row id breaks a tie within the millisecond"
      (Cursor.after { ms := 5, seq := 2 } { ms := 5, seq := 1 } = true) <|
    test "and the order is antisymmetric"
      (Cursor.after { ms := 5, seq := 1 } { ms := 5, seq := 2 } = false)

/-! ## Configuration -/

private def envOf (pairs : List (String × String)) : String → Option String :=
  fun name => (pairs.find? (·.1 == name)).map (·.2)

private def configTests : TestSeq :=
  let bare := ServerConfig.ofEnv (envOf [("HOME", "/home/someone")])
  let localNode := ServerConfig.ofEnv (envOf [("TRUST_LOCAL", "1"), ("HOME", "/home/someone")])
  let tuned := ServerConfig.ofEnv (envOf [
    ("HOME", "/home/someone"),
    ("PORT", "9000"),
    ("PUBLIC_URL", "https://trust.example.org///"),
    ("NODE_NAME", "example"),
    ("FEDERATION_SEEDS", " https://a.example , ,https://b.example "),
    ("FEDERATION_MAX_DEPTH", "5"),
    ("FEDERATION_MAX_ENTRIES", "not a number"),
    ("FEDERATION_AUTODISCOVER", "yes"),
    ("ADMIN_TOKEN", "s3cret")])
  group "configuration" <|
    group "the defaults of §8" (
      test "maxDepth" (bare.policy.maxDepth = 2) <|
      test "maxEntries" (bare.policy.maxEntries = 500) <|
      test "maxResponseBytes is 2 MiB" (bare.policy.maxResponseBytes = 2097152) <|
      test "peerTimeoutMs" (bare.policy.peerTimeoutMs = 4000) <|
      test "queryBudgetMs" (bare.policy.queryBudgetMs = 8000) <|
      test "remoteTtlS" (bare.policy.remoteTtlS = 300) <|
      test "maxViaLength" (bare.policy.maxViaLength = 8) <|
      test "autodiscover is off" (bare.policy.autodiscover = false) <|
      test "allowPrivate is off" (bare.policy.allowPrivate = false)) <|
    group "local mode" (
      test "gets its own port" (localNode.port = 8090) <|
      test "names itself" (localNode.name = "local") <|
      test "knows its own URL" (localNode.publicUrl = "http://127.0.0.1:8090") <|
      test "allows private addresses, which is what it is for"
        (localNode.policy.allowPrivate = true) <|
      test "and needs no GitHub app to start" (localNode.problems.size = 0)) <|
    group "the environment" (
      test "the port is read" (tuned.port = 9000) <|
      test "trailing slashes come off a URL"
        (tuned.publicUrl = "https://trust.example.org") <|
      test "seeds are split and trimmed" (tuned.seeds.size = 2) <|
      test "and keep their order" (tuned.seeds[0]! = "https://a.example") <|
      test "a limit is overridden" (tuned.policy.maxDepth = 5) <|
      test "an unparseable limit falls back rather than becoming zero"
        (tuned.policy.maxEntries = 500) <|
      test "`yes` is true" (tuned.policy.autodiscover = true) <|
      test "the store path defaults under HOME"
        (bare.storeDir = "/home/someone/.local/share/trust/store")) <|
    group "refusing to start misconfigured" (
      test "a public node with nothing configured is refused"
        (bare.problems.size = 4) <|
      test "and one with a URL and a token still needs the rest"
        (tuned.problems.size = 3)) <|
    group "§8 onto Std.Http.Config" (
      test "maxResponseBytes becomes maxBodySize"
        (bare.httpConfig.maxBodySize = bare.policy.maxResponseBytes) <|
      -- The timeouts deliberately keep their Std.Http defaults; see the comment
      -- on `httpConfig` for why mapping peerTimeoutMs onto one would be wrong.
      test "and the inbound timeouts are left alone"
        (bare.httpConfig.headerTimeout.val = (5000 : Int)))

/-! ## The store -/

/-- What one store run found out; the assertions are made about this afterwards. -/
private structure StoreFindings where
  roundTripAsserted : String
  roundTripNote : String
  roundTripHints : String
  reopenedAsserted : String
  reopenedCount : Nat
  earlierIsKept : PutOutcome
  laterReplaces : PutOutcome
  tieKeeps : PutOutcome
  winnerAsserted : String
  visibleBeforeRevocation : Nat
  suppressedByRevocation : Bool
  reinstatedByLaterCertificate : Bool
  suppressedVisibleWhenAsked : Nat
  visibleAfterRevocation : Nat
  visibleAfterReissue : Nat
  orphanRevocationKept : Bool
  orphanSuppressesOnArrival : Bool
  laterRevocationWins : String
  earlierRevocationLoses : String
  discovered : String
  admitted : String
  blockedStaysBlocked : String
  seedStaysSeed : String
  queriedCount : Nat
  totalWritten : Nat
  paged : Nat
  pagesSeen : Nat
  cursorsStrictlyIncreasing : Bool
  noDuplicates : Bool
  resumeFromEndIsEmpty : Bool
  resumeFromEndKeepsCursor : Bool
  finalPageComplete : Bool
  sameMillisecondRows : Nat
  compactedFrom : Nat
  compactedTo : Nat
  liveAfterCompaction : Nat
  survivesCompactionAndReopen : String
  tombstoneOnPage : Bool
  certificateGoneAfterDelete : Bool

private def runStore (root : System.FilePath) : IO StoreFindings := do
  -- Durable by default: this is the write path a node actually runs.
  let dir := root / "store"
  let store ← Store.open dir

  -- Append and read back.
  let _ ← store.putCertificate (certOf fpA hash1 "2024-01-01T00:00:00Z")
  let stored ← store.getCertificate fpA hash1 "semantic_hash/1"
  let roundTripAsserted := (stored.map (·.entry.claim.asserted)).getD "<missing>"
  let roundTripNote := (stored.map (·.entry.claim.note)).getD "<missing>"
  let roundTripHints := (stored.map (·.hints.issuer)).getD "<missing>"

  -- §3.5, in three directions.  An earlier assertion loses, a later one wins,
  -- and an exact tie keeps what is stored so that gossip converges.
  let earlierIsKept ← store.putCertificate (certOf fpA hash1 "2023-06-01T00:00:00Z")
  let laterReplaces ← store.putCertificate (certOf fpA hash1 "2024-07-01T00:00:00Z")
  let tieKeeps ← store.putCertificate
    { certOf fpA hash1 "2024-07-01T00:00:00Z" with fromPeer := "https://elsewhere.example" }
  let winner ← store.getCertificate fpA hash1 "semantic_hash/1"
  let winnerAsserted := (winner.map (·.entry.claim.asserted)).getD "<missing>"
  -- The tie kept the stored row, so the losing copy's `fromPeer` is not there.
  let tieKeptStored := (winner.map (·.fromPeer)).getD "<missing>"

  -- The same hash under a different hasher is a different entry, never a collision.
  let _ ← store.putCertificate (certOf fpA hash1 "2020-01-01T00:00:00Z" (hasher := "other/1"))

  -- §6.2.  A revocation suppresses what was asserted no later than it; a later
  -- certificate reinstates without any second message.
  let visibleBefore ← store.certificatesByHash hash1 (some "semantic_hash/1")
  let _ ← store.putRevocation (revOf fpA hash1 "2024-08-01T00:00:00Z")
  let suppressed ← store.isRevoked fpA hash1 "semantic_hash/1" "2024-07-01T00:00:00Z"
  let visibleAfterRevocation ← store.certificatesByHash hash1 (some "semantic_hash/1")
  let suppressedVisible ←
    store.certificatesByHash hash1 (some "semantic_hash/1") (includeRevoked := true)
  let _ ← store.putCertificate (certOf fpA hash1 "2024-09-01T00:00:00Z")
  let reinstated ← store.isRevoked fpA hash1 "semantic_hash/1" "2024-09-01T00:00:00Z"
  let visibleAfterReissue ← store.certificatesByHash hash1 (some "semantic_hash/1")

  -- §6 rule 4: a withdrawal for a certificate this node has never seen is kept,
  -- and bites when the certificate turns up afterwards by another path.
  let _ ← store.putRevocation (revOf fpB hash2 "2024-03-01T00:00:00Z")
  let orphanKept := (← store.getRevocation fpB hash2 "semantic_hash/1").isSome
  let _ ← store.putCertificate (certOf fpB hash2 "2024-02-01T00:00:00Z")
  let orphanSuppresses ← store.isRevoked fpB hash2 "semantic_hash/1" "2024-02-01T00:00:00Z"

  -- A revocation is superseded the same way a certificate is.
  let _ ← store.putRevocation (revOf fpB hash2 "2024-04-01T00:00:00Z")
  let laterRevocationWins :=
    ((← store.getRevocation fpB hash2 "semantic_hash/1").map (·.revocation.revoked)).getD "<none>"
  let _ ← store.putRevocation (revOf fpB hash2 "2024-01-01T00:00:00Z")
  let earlierRevocationLoses :=
    ((← store.getRevocation fpB hash2 "semantic_hash/1").map (·.revocation.revoked)).getD "<none>"

  -- §5.1's four states, and what discovery may do to each.
  store.putPeer { url := "https://seed.example", name := "seed", status := .seed }
  store.putPeer { url := "https://blocked.example", name := "blocked", status := .blocked }
  let discovered ← store.discoverPeer "https://new.example" "new" (autodiscover := false)
  let admitted ← store.discoverPeer "https://admitted.example" "admitted" (autodiscover := true)
  let blockedAgain ← store.discoverPeer "https://blocked.example" "blocked" (autodiscover := true)
  let seedAgain ← store.discoverPeer "https://seed.example" "seed" (autodiscover := true)
  store.notePeerSeen "https://seed.example" "17.3" ""
  let queried ← store.queriedPeers

  -- Restart: everything above has to come back out of the files.
  store.flush
  let reopened ← Store.open dir
  let reopenedCert ← reopened.getCertificate fpA hash1 "semantic_hash/1"
  let reopenedAsserted := (reopenedCert.map (·.entry.claim.asserted)).getD "<missing>"
  let reopenedAll ← reopened.certificatesSince "" 1000
  let reopenedCount := reopenedAll.values.size

  -- Paging.  `fsync := false` here so that the writes land faster than the
  -- clock ticks: rows sharing a millisecond are exactly the case the row id
  -- exists for, and a durable write would spread them out and never test it.
  let pagedDir := root / "paged"
  let pager ← Store.open pagedDir { fsync := false }
  let total := 137
  let limit := 25
  for i in [0:total] do
    let hash := String.ofList (Nat.toDigits 16 (0x1000 + i))
    let _ ← pager.putCertificate (certOf fpA hash "2024-01-01T00:00:00Z")
  let allRows := (← pager.certificatesSince "" 10000).rows
  let sameMillisecond := Id.run do
    let mut n := 0
    for i in [1:allRows.size] do
      if allRows[i]!.updatedAt == allRows[i-1]!.updatedAt then n := n + 1
    return n
  let mut cursor := ""
  let mut seen : Array String := #[]
  let mut cursors : Array Cursor := #[]
  let mut pages := 0
  let mut complete := false
  repeat
    let page ← pager.certificatesSince cursor limit
    pages := pages + 1
    for row in page.rows do
      seen := seen.push row.key
      cursors := cursors.push row.cursor
    cursor := page.cursor
    if page.complete then
      complete := true
      break
    if pages > 100 then break
  let strictlyIncreasing := Id.run do
    let mut ok := true
    for i in [1:cursors.size] do
      if !cursors[i]!.after cursors[i-1]! then ok := false
    return ok
  let noDuplicates :=
    (seen.foldl (fun (m : Std.HashMap String Unit) k => m.insert k ()) {}).size == seen.size
  let tail ← pager.certificatesSince cursor limit
  let resumeEmpty := tail.rows.isEmpty
  let resumeKeepsCursor := tail.cursor == cursor

  -- Compaction.  The paged store has one row per key, so a separate store is
  -- churned by hammering a single key.
  let churnDir := root / "churn"
  let churn ← Store.open churnDir { fsync := false }
  for i in [0:40] do
    let seconds := if i < 10 then s!"0{i}" else s!"{i}"
    let _ ← churn.putCertificate (certOf fpA hash1 s!"2024-01-01T00:00:{seconds}Z")
  let _ ← churn.putCertificate (certOf fpB hash2 "2024-01-01T00:00:00Z")
  churn.deleteCertificate fpB hash2 "semantic_hash/1"
  let (beforeTotal, _) ← churn.certificateLogSize
  churn.compact
  let (afterTotal, afterLive) ← churn.certificateLogSize
  -- A tombstone stays on the page after compaction: a peer that only ever saw
  -- present rows would never learn the row went away.
  let churnPage ← churn.certificatesSince "" 1000
  let tombstoneOnPage := churnPage.rows.any (·.value.isNone)
  let goneAfterDelete := (← churn.getCertificate fpB hash2 "semantic_hash/1").isNone
  churn.flush
  let churnReopened ← Store.open churnDir { fsync := false }
  let survives :=
    ((← churnReopened.getCertificate fpA hash1 "semantic_hash/1").map
      (·.entry.claim.asserted)).getD "<missing>"

  return {
    roundTripAsserted, roundTripNote, roundTripHints
    reopenedAsserted, reopenedCount
    earlierIsKept, laterReplaces, tieKeeps
    winnerAsserted := s!"{winnerAsserted}|{tieKeptStored}"
    visibleBeforeRevocation := visibleBefore.size
    suppressedByRevocation := suppressed
    reinstatedByLaterCertificate := !reinstated
    suppressedVisibleWhenAsked := suppressedVisible.size
    visibleAfterRevocation := visibleAfterRevocation.size
    visibleAfterReissue := visibleAfterReissue.size
    orphanRevocationKept := orphanKept
    orphanSuppressesOnArrival := orphanSuppresses
    laterRevocationWins, earlierRevocationLoses
    discovered := discovered.toString
    admitted := admitted.toString
    blockedStaysBlocked := blockedAgain.toString
    seedStaysSeed := seedAgain.toString
    queriedCount := queried.size
    totalWritten := total
    paged := seen.size
    pagesSeen := pages
    cursorsStrictlyIncreasing := strictlyIncreasing
    noDuplicates
    resumeFromEndIsEmpty := resumeEmpty
    resumeFromEndKeepsCursor := resumeKeepsCursor
    finalPageComplete := complete
    sameMillisecondRows := sameMillisecond
    compactedFrom := beforeTotal
    compactedTo := afterTotal
    liveAfterCompaction := afterLive
    survivesCompactionAndReopen := survives
    tombstoneOnPage
    certificateGoneAfterDelete := goneAfterDelete }

private def storeTests (f : StoreFindings) : TestSeq :=
  group "the store" <|
    group "append and read back" (
      test "the claim comes back" (f.roundTripAsserted = "2024-01-01T00:00:00Z") <|
      test "a note with a quote and a newline survives one line of JSONL"
        (f.roundTripNote = "he said \"fine\", then\na newline") <|
      test "hints are kept, unverified, for display" (f.roundTripHints = "alice")) <|
    group "restart" (
      test "the log is the state: reopening the directory finds the same entry"
        (f.reopenedAsserted = "2024-09-01T00:00:00Z") <|
      test "and every live row, superseded ones collapsed" (f.reopenedCount = 3)) <|
    group "§3.5 identity and replacement" (
      test "an earlier assertion does not displace a later one"
        (f.earlierIsKept = PutOutcome.kept) <|
      test "a later assertion replaces" (f.laterReplaces = PutOutcome.replaced) <|
      test "a tie keeps what is stored, so gossip converges"
        (f.tieKeeps = PutOutcome.kept) <|
      test "and the stored row really is the one that was kept"
        (f.winnerAsserted = "2024-07-01T00:00:00Z|") <|
      test "the same hash under another hasher is a separate entry"
        (f.visibleBeforeRevocation = 1)) <|
    group "§6.2 revocation" (
      test "a certificate asserted no later than the revocation is suppressed"
        (f.suppressedByRevocation = true) <|
      test "and disappears from a query" (f.visibleAfterRevocation = 0) <|
      test "but is still there when the caller asks for it"
        (f.suppressedVisibleWhenAsked = 1) <|
      test "a later certificate reinstates, with no second message"
        (f.reinstatedByLaterCertificate = true) <|
      test "and comes back to the query" (f.visibleAfterReissue = 1) <|
      test "a revocation for an unseen certificate is kept (rule 4)"
        (f.orphanRevocationKept = true) <|
      test "and suppresses that certificate when it arrives afterwards"
        (f.orphanSuppressesOnArrival = true) <|
      test "a later revocation supersedes"
        (f.laterRevocationWins = "2024-04-01T00:00:00Z") <|
      test "an earlier one does not"
        (f.earlierRevocationLoses = "2024-04-01T00:00:00Z")) <|
    group "§5.1 peer states" (
      test "discovery proposes a candidate when autodiscover is off"
        (f.discovered = "candidate") <|
      test "and an active peer when it is on" (f.admitted = "active") <|
      test "blocked is absorbing: discovery never re-admits"
        (f.blockedStaysBlocked = "blocked") <|
      test "a seed stays a seed" (f.seedStaysSeed = "seed") <|
      test "§5.3 lists only what this node queries itself" (f.queriedCount = 2)) <|
    group "§4.3 cursor paging" (
      test "every row is seen" (f.paged = f.totalWritten) <|
      test "and none of them twice" (f.noDuplicates = true) <|
      test "it really did take several pages" (f.pagesSeen = 6) <|
      test "cursors are strictly increasing, so the order is total"
        (f.cursorsStrictlyIncreasing = true) <|
      test "rows do share a millisecond, which is the case the row id is for"
        (f.sameMillisecondRows > 0) <|
      test "the last page says it is complete" (f.finalPageComplete = true) <|
      test "resuming from the end returns nothing" (f.resumeFromEndIsEmpty = true) <|
      test "and hands back the same cursor rather than rewinding"
        (f.resumeFromEndKeepsCursor = true)) <|
    group "compaction" (
      test "the log was much longer than what it said" (f.compactedFrom = 42) <|
      test "and is rewritten to one row per key" (f.compactedTo = 2) <|
      test "which is what the index holds" (f.liveAfterCompaction = 2) <|
      test "a tombstone stays, so a delete still reaches a peer"
        (f.tombstoneOnPage = true) <|
      test "the deleted row is gone from the index"
        (f.certificateGoneAfterDelete = true) <|
      test "and the live data survives compaction and a reopen"
        (f.survivesCompactionAndReopen = "2024-01-01T00:00:39Z"))

/-! ## The server

Everything below runs against a real server on a real socket, and against real
OpenPGP signatures made by a real `gpg` in a throwaway home directory.  A test
that mocked the signature would be testing the mock: §3.4 is almost entirely a
statement about what a signature does, and the interesting failures — a subkey
signature, a tampered claim, a withdrawal signed by the wrong key — only exist
once the cryptography is real.

Two nodes run in one process: one in local mode, which is where publishing and
reading are exercised, and one public node with an operator token, which is
where the import endpoint's authentication and the bearer-token and cookie
sessions are.
-/

/-- Lean has no HTTP client, and curl is not a dependency of the tests. -/
private structure Reply where
  status : Nat
  body : String
  raw : String
  deriving Inhabited

private def statusOf (raw : String) : Nat :=
  match (raw.splitOn "\r\n").headD "" |>.splitOn " " with
  | _ :: code :: _ => code.toNat?.getD 0
  | _ => 0

/-- Everything after the blank line.  `Std.Http` answers with a `Content-Length`. -/
private def bodyOf (raw : String) : String :=
  match raw.splitOn "\r\n\r\n" with
  | _ :: rest => String.intercalate "\r\n\r\n" rest
  | [] => ""

private def request (port : Nat) (method path : String) (body : String := "")
    (headers : Array (String × String) := #[]) : Async Reply := do
  let client ← TCP.Socket.Client.mk
  client.connect (SocketAddress.v4 {
    addr := IPv4Addr.ofParts 127 0 0 1, port := UInt16.ofNat port })
  let mut head := s!"{method} {path} HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n"
  for (name, value) in headers do
    head := head ++ s!"{name}: {value}\r\n"
  if !body.isEmpty then
    -- The length is in bytes, not characters: an armoured key is ASCII but a
    -- note need not be, and a short count truncates the body server-side.
    head := head ++ s!"Content-Type: application/json\r\nContent-Length: {body.toUTF8.size}\r\n"
  client.send (head ++ "\r\n" ++ body).toUTF8
  let mut out := ByteArray.empty
  repeat
    match ← client.recv? 4096 with
    | some chunk => if chunk.isEmpty then break else out := out ++ chunk
    | none => break
  let raw := String.fromUTF8! out
  return { status := statusOf raw, body := bodyOf raw, raw }

/-! ### Reading answers -/

private def parsed (reply : Reply) : Json := (Json.parse reply.body).toOption.getD Json.null
private def jStr (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
private def jNat (j : Json) (k : String) : Nat := (j.getObjValAs? Nat k).toOption.getD 0
private def jBool (j : Json) (k : String) : Bool := (j.getObjValAs? Bool k).toOption.getD false
private def jSub (j : Json) (k : String) : Json := (j.getObjVal? k).toOption.getD Json.null
private def jArr (j : Json) (k : String) : Array Json :=
  ((j.getObjVal? k).bind (·.getArr?)).toOption.getD #[]

private def contains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-! ### Real keys -/

private structure TestKey where
  primary : String
  armoredPublic : String
  armoredPrivate : String
  deriving Inhabited

private def gpgIn (home : System.FilePath) (args : Array String) (stdin : String := "") :
    IO (UInt32 × String) := do
  let child ← IO.Process.spawn {
    cmd := "gpg",
    args := #["--homedir", home.toString, "--batch", "--quiet", "--no-tty",
              "--passphrase", "", "--pinentry-mode", "loopback"] ++ args,
    stdin := .piped, stdout := .piped, stderr := .piped }
  let (h, child) ← child.takeStdin
  h.putStr stdin
  h.flush
  let out ← IO.asTask child.stdout.readToEnd .dedicated
  let _ ← child.stderr.readToEnd
  let code ← child.wait
  return (code, ← IO.ofExcept out.get)

private def primaryIn (listing : String) : String := Id.run do
  let mut afterPub := false
  for line in listing.splitOn "\n" do
    if line.startsWith "pub:" then afterPub := true
    else if line.startsWith "sub:" then afterPub := false
    else if line.startsWith "fpr:" && afterPub then
      let fields := line.splitOn ":"
      if h : 9 < fields.length then return fields[9].toLower
  return ""

/--
A key with a separate signing subkey.

`--quick-gen-key` alone leaves a key whose primary does the signing, which is
the easy case.  The ordinary case is a signing subkey, so that the fingerprint
on the signature is not the fingerprint on the entry — §3.4 rule 5, and the rule
`FEDERATION.md` calls the one most easily got wrong.
-/
private def makeKey (home : System.FilePath) (uid : String) : IO TestKey := do
  let _ ← gpgIn home #["--quick-gen-key", uid, "ed25519", "sign", "never"]
  let (_, listing0) ← gpgIn home #["--with-colons", "--list-keys", uid]
  let _ ← gpgIn home #["--quick-add-key", primaryIn listing0, "ed25519", "sign", "never"]
  let (_, listing) ← gpgIn home #["--with-colons", "--list-keys", uid]
  let (_, pub) ← gpgIn home #["--armor", "--export", uid]
  let (_, secret) ← gpgIn home #["--armor", "--export-secret-keys", uid]
  return { primary := primaryIn listing, armoredPublic := pub, armoredPrivate := secret }

private def signWith (home : System.FilePath) (uid text : String) : IO String := do
  let (_, sig) ← gpgIn home #["--armor", "--detach-sign", "--local-user", uid, "--output", "-"] text
  return sig

/-! ### Fixtures -/

private def claimOf (decl hash asserted : String) (note : String := "") : Trust.Claim :=
  { decl, hash, hasher := "semantic_hash/1"
    repo := "github.com/chrisflav/trust"
    commit := "1cbfa56f28cf6cb9acdc0ff338e4d32bceee4fa3"
    toolchain := "leanprover/lean4:v4.32.0"
    asserted, note }

private def publishBody (claim : Trust.Claim) (signature : String := "") : String :=
  Json.compress <| Json.mkObj <|
    [("claim", toJson claim)] ++
      (if signature.isEmpty then [] else [("signature", Json.str signature)])

private def revocationBody (revocation : Trust.Revocation) (signature key : String) : String :=
  Json.compress <| Json.mkObj [
    ("revocation", toJson revocation), ("signature", Json.str signature), ("key", Json.str key)]

/-- The port the OS chose, which is the only one a test may use. -/
private def portOf (server : Server) : Nat :=
  match server.localAddr with
  | some (.v4 a) => a.port.toNat
  | some (.v6 a) => a.port.toNat
  | none => 0

/--
A node, with the routes it is asked to answer on.

Built here rather than taken from `TrustServer.serve`, which still answers with
the skeleton handler: wiring the router into the server is the orchestrator's
change, and this is the same `router` that it will make.

The app arrives in a ref rather than as a value because a federating node cannot
be finished before it is bound — it does not know its own URL until the OS has
picked a port, and §5.2 and §7.1 both turn on a node knowing its own URL.
-/
private def serveRoutes (config : ServerConfig) (app : IO.Ref App) (routes : Array Route) :
    Async Server := do
  let addr := SocketAddress.v4 {
    addr := IPv4Addr.ofParts 127 0 0 1, port := UInt16.ofNat config.port }
  Server.serve addr
    ({ onRequest := fun req => do (router (← app.get) routes).onRequest req } :
      Server.StatelessHandler)
    config.httpConfig

/-! ### What one run found out -/

private structure RouteFindings where
  gpgAvailable : Bool := true
  healthOk : Bool := false
  healthName : String := ""
  descriptorUrl : String := ""
  descriptorProtocol : String := ""
  meLogin : String := ""
  meLocal : Bool := false
  keyFingerprint : String := ""
  keyVerifiedVia : String := ""
  keyLookedUp : String := ""
  privateKeyStatus : Nat := 0
  privateKeyError : String := ""
  publishSignedStatus : Nat := 0
  publishSignedAssurance : String := ""
  readBackCount : Nat := 0
  readBackCanonical : String := ""
  expectedCanonical : String := ""
  readBackAssurance : String := ""
  readBackFingerprint : String := ""
  expectedFingerprint : String := ""
  readBackVerifiedHere : Bool := false
  readBackKeyPresent : Bool := false
  badSignatureStatus : Nat := 0
  badSignatureError : String := ""
  attestedAssurance : String := ""
  attestedVisible : Nat := 0
  exportSignedPresent : Bool := false
  exportAttestedPresent : Bool := true
  exportEntryHasHints : Bool := false
  revocationStatus : Nat := 0
  revocationCanonical : String := ""
  expectedRevocationCanonical : String := ""
  visibleAfterRevocation : Nat := 0
  visibleAfterReissue : Nat := 0
  forgedRevocationStatus : Nat := 0
  forgedRevocationError : String := ""
  pagedTotal : Nat := 0
  pagedSeen : Nat := 0
  pagedPages : Nat := 0
  pagedNoRepeats : Bool := false
  firstPageComplete : Bool := true
  lastPageComplete : Bool := false
  importUnauthenticatedStatus : Nat := 0
  importAccepted : Nat := 0
  importRejected : Nat := 0
  importReasons : Nat := 0
  importReason : String := ""
  importedVisible : Nat := 0
  importedAssurance : String := ""
  importedLocal : Bool := true
  importedKeyVerifiedVia : String := ""
  importedProtocolStatus : Nat := 0
  publishWithoutCredentialStatus : Nat := 0
  publishWithBogusTokenStatus : Nat := 0
  publishWithTokenAssurance : String := ""
  tokenListedCount : Nat := 0
  tokenSecretWithheld : Bool := false
  cookieAssurance : String := ""
  afterLogoutStatus : Nat := 0
  expiredCookieStatus : Nat := 0
  trustKeysCount : Nat := 0
  trustedHashCount : Nat := 0
  badFingerprintStatus : Nat := 0
  unknownLoginStatus : Nat := 0
  unknownPathStatus : Nat := 0
  wrongMethodStatus : Nat := 0
  shutDownCleanly : Bool := false
  deriving Inhabited

/-! ### The run -/

private def runRoutes (root : System.FilePath) : IO RouteFindings := do
  if !(← Trust.defaultVerifier.available) then
    return { gpgAvailable := false }
  IO.FS.withTempDir fun home => do
    let alice ← makeKey home "Alice Routes <alice@example.org>"
    let mallory ← makeKey home "Mallory Routes <mallory@example.org>"

    let localStore ← Store.open (root / "node-one") { fsync := false }
    let publicStore ← Store.open (root / "node-two") { fsync := false }
    -- §9: one identity, no OAuth.  The public node is the one that has to say no.
    let localConfig : ServerConfig := {
      port := 0, name := "alice", localMode := true, publicUrl := "http://one.test" }
    let publicConfig : ServerConfig := {
      port := 0, name := "two", localMode := false, publicUrl := "http://two.test",
      adminToken := "operator-token" }

    -- A browser session and a command-line token, written straight into the
    -- store: the rows are what a session *is* here, so this is the whole of what
    -- the OAuth callback would have left behind, without needing a GitHub app.
    publicStore.putIdentity { login := "bob", githubId := 4711 }
    let bobToken := "trust_" ++ (← freshToken)
    publicStore.putSession { token := bobToken, id := "tok-1", kind := .api, login := "bob",
                             name := "laptop" }
    let bobCookie ← freshToken
    publicStore.putSession { token := bobCookie, id := "ses-1", kind := .browser, login := "bob",
                             expiresMs := (← nowMs) + 60000 }
    let staleCookie ← freshToken
    publicStore.putSession { token := staleCookie, id := "ses-2", kind := .browser, login := "bob",
                             expiresMs := (← nowMs) - 1 }

    let oneApp ← IO.mkRef ({ config := localConfig, store := localStore } : App)
    let twoApp ← IO.mkRef ({ config := publicConfig, store := publicStore } : App)
    let served := Routes.certificateRoutes ++ Auth.sessionRoutes
    Async.block do
      let one ← serveRoutes localConfig oneApp served
      let two ← serveRoutes publicConfig twoApp served
      let p1 := portOf one
      let p2 := portOf two
      let mut f : RouteFindings := {}

      let health ← request p1 "GET" "/api/health"
      f := { f with healthOk := jBool (parsed health) "ok", healthName := jStr (parsed health) "name" }
      let descriptor ← request p1 "GET" "/api/federation"
      f := { f with
        descriptorUrl := jStr (parsed descriptor) "url"
        descriptorProtocol := jStr (parsed descriptor) "protocol" }
      let me ← request p1 "GET" "/api/me"
      f := { f with
        meLogin := jStr (jSub (parsed me) "user") "login", meLocal := jBool (parsed me) "local" }

      -- Keys.  The public half is registered; the private half is refused, and
      -- refused on the text before anything is asked to parse it.
      let registered ← request p1 "POST" "/api/keys"
        (Json.compress (Json.mkObj [("armored", Json.str alice.armoredPublic)]))
      f := { f with
        keyFingerprint := jStr (parsed registered) "fingerprint"
        keyVerifiedVia := jStr (parsed registered) "verifiedVia" }
      let refused ← request p1 "POST" "/api/keys"
        (Json.compress (Json.mkObj [("armored", Json.str alice.armoredPrivate)]))
      f := { f with
        privateKeyStatus := refused.status, privateKeyError := jStr (parsed refused) "error" }
      let lookedUp ← request p1 "GET" s!"/api/key/{alice.primary}"
      f := { f with keyLookedUp := jStr (parsed lookedUp) "login" }

      -- Publish, signed, and read it back.
      let claimA := claimOf "Foo.a" "00000000000000a1" "2024-01-01T00:00:00Z" "quote \" and\nnewline"
      let sigA ← signWith home "alice@example.org" claimA.canonical
      let published ← request p1 "POST" "/api/certificates" (publishBody claimA sigA)
      f := { f with
        publishSignedStatus := published.status
        publishSignedAssurance := jStr (parsed published) "assurance" }
      let read ← request p1 "GET" s!"/api/certificates?hash={claimA.hash}&hasher=semantic_hash/1"
      let rows := jArr (parsed read) "certificates"
      f := { f with
        readBackCount := rows.size
        expectedCanonical := claimA.canonical
        readBackCanonical := jStr (rows[0]!) "canonical"
        readBackAssurance := jStr (rows[0]!) "assurance"
        readBackFingerprint := jStr (rows[0]!) "fingerprint"
        expectedFingerprint := alice.primary
        readBackKeyPresent := contains (jStr (rows[0]!) "key") "BEGIN PGP PUBLIC KEY BLOCK"
        readBackVerifiedHere := jBool (jSub (rows[0]!) "provenance") "verifiedHere" }

      -- A signature over other bytes is not a signature over this claim.
      let claimB := claimOf "Foo.b" "00000000000000b2" "2024-01-01T00:00:00Z"
      let wrongSig ← signWith home "alice@example.org" (claimOf "Foo.b" "00000000000000b2"
        "2024-01-01T00:00:00Z" "different bytes").canonical
      let refusedEntry ← request p1 "POST" "/api/certificates" (publishBody claimB wrongSig)
      f := { f with
        badSignatureStatus := refusedEntry.status
        badSignatureError := jStr (parsed refusedEntry) "error" }

      -- Unsigned: stored, marked, and never exported.
      let claimC := claimOf "Foo.c" "00000000000000c3" "2024-02-01T00:00:00Z"
      let attested ← request p1 "POST" "/api/certificates" (publishBody claimC)
      let attestedRead ← request p1 "GET" s!"/api/certificates?hash={claimC.hash}"
      f := { f with
        attestedAssurance := jStr (parsed attested) "assurance"
        attestedVisible := (jArr (parsed attestedRead) "certificates").size }

      let exported ← request p1 "GET" "/api/certificates/export?limit=500"
      let exportedEntries := jArr (parsed exported) "entries"
      f := { f with
        exportSignedPresent := exportedEntries.any fun e => jStr (jSub e "claim") "hash" == claimA.hash
        exportAttestedPresent :=
          exportedEntries.any fun e => jStr (jSub e "claim") "hash" == claimC.hash
        exportEntryHasHints := exportedEntries.any fun e => jStr (jSub e "hints") "issuer" == "alice" }

      -- §6.  A withdrawal signed by the key that made the assertion.
      let revocation : Trust.Revocation := {
        fingerprint := alice.primary, hash := claimA.hash, hasher := "semantic_hash/1",
        reason := "the proof was wrong", revoked := "2024-06-01T00:00:00Z" }
      let revSig ← signWith home "alice@example.org" revocation.canonical
      let withdrawn ← request p1 "POST" "/api/revocations"
        (revocationBody revocation revSig alice.armoredPublic)
      let afterRevocation ← request p1 "GET" s!"/api/certificates?hash={claimA.hash}"
      f := { f with
        revocationStatus := withdrawn.status
        revocationCanonical := jStr (parsed withdrawn) "canonical"
        expectedRevocationCanonical := revocation.canonical
        visibleAfterRevocation := (jArr (parsed afterRevocation) "certificates").size }

      -- §6.2 rule 3: re-issuing afterwards reinstates, with no second message.
      let claimA' := { claimA with asserted := "2024-09-01T00:00:00Z" }
      let sigA' ← signWith home "alice@example.org" claimA'.canonical
      let _ ← request p1 "POST" "/api/certificates" (publishBody claimA' sigA')
      let afterReissue ← request p1 "GET" s!"/api/certificates?hash={claimA.hash}"
      f := { f with visibleAfterReissue := (jArr (parsed afterReissue) "certificates").size }

      -- A withdrawal of somebody else's assertion, signed by the wrong key.
      let forgedSig ← signWith home "mallory@example.org" revocation.canonical
      let forged ← request p1 "POST" "/api/revocations"
        (revocationBody revocation forgedSig mallory.armoredPublic)
      f := { f with
        forgedRevocationStatus := forged.status
        forgedRevocationError := jStr (parsed forged) "error" }

      -- §4.1 paging: more entries than `limit`, resumed from the cursor.
      for i in [0:5] do
        let claim := claimOf s!"Foo.p{i}" s!"00000000000000d{i}" "2024-03-01T00:00:00Z"
        let sig ← signWith home "alice@example.org" claim.canonical
        let _ ← request p1 "POST" "/api/certificates" (publishBody claim sig)
      let everything ← request p1 "GET" "/api/certificates/export?limit=500"
      let total := (jArr (parsed everything) "entries").size
      let mut cursor := ""
      let mut seen : Array String := #[]
      let mut pages := 0
      let mut firstComplete := true
      let mut lastComplete := false
      repeat
        let page ← request p1 "GET" s!"/api/certificates/export?limit=2&since={cursor}"
        let body := parsed page
        pages := pages + 1
        if pages == 1 then firstComplete := jBool body "complete"
        for entry in jArr body "entries" do
          seen := seen.push (jStr (jSub entry "claim") "hash" ++ "|" ++ jStr entry "fingerprint")
        cursor := jStr body "cursor"
        if jBool body "complete" then
          lastComplete := true
          break
        if pages > 40 then break
      f := { f with
        pagedTotal := total, pagedSeen := seen.size, pagedPages := pages
        pagedNoRepeats :=
          (seen.foldl (fun (m : Std.HashMap String Unit) k => m.insert k ()) {}).size == seen.size
        firstPageComplete := firstComplete, lastPageComplete := lastComplete }

      -- §4.2 import, on the node that has to authenticate it.
      let bundle := parsed everything
      let tampered : Json :=
        match (jArr bundle "entries")[0]? with
        | some entry =>
          let claim := jSub entry "claim"
          Json.mkObj [
            ("claim", Json.mkObj [
              ("decl", Json.str (jStr claim "decl")), ("hash", Json.str (jStr claim "hash")),
              ("hasher", Json.str (jStr claim "hasher")), ("repo", Json.str (jStr claim "repo")),
              ("commit", Json.str (jStr claim "commit")),
              ("toolchain", Json.str (jStr claim "toolchain")),
              ("asserted", Json.str (jStr claim "asserted")),
              ("note", Json.str "tampered after signing")]),
            ("signature", Json.str (jStr entry "signature")),
            ("key", Json.str (jStr entry "key")),
            ("fingerprint", Json.str (jStr entry "fingerprint"))]
        | none => Json.null
      let pushed := Json.compress <| Json.mkObj [
        ("protocol", Json.str "trust/1"), ("origin", Json.str "http://one.test"),
        ("entries", Json.arr ((jArr bundle "entries").push tampered)),
        ("revocations", Json.arr (jArr bundle "revocations")),
        ("complete", Json.bool true)]
      let unauthenticated ← request p2 "POST" "/api/import" pushed
      let imported ← request p2 "POST" "/api/import" pushed
        #[("Authorization", "Bearer operator-token")]
      let wrongProtocol ← request p2 "POST" "/api/import"
        (Json.compress (Json.mkObj [("protocol", Json.str "trust/9")]))
        #[("Authorization", "Bearer operator-token")]
      let relayed ← request p2 "GET" s!"/api/certificates?hash={claimA.hash}"
      let relayedRows := jArr (parsed relayed) "certificates"
      f := { f with
        importUnauthenticatedStatus := unauthenticated.status
        importAccepted := jNat (parsed imported) "accepted"
        importRejected := jNat (parsed imported) "rejected"
        importReasons := (jArr (parsed imported) "reasons").size
        importReason := ((jArr (parsed imported) "reasons")[0]?).map (·.getStr?.toOption.getD "")
          |>.getD ""
        importedProtocolStatus := wrongProtocol.status
        importedVisible := relayedRows.size
        importedAssurance := jStr (relayedRows[0]!) "assurance"
        importedLocal := jBool (jSub (relayedRows[0]!) "provenance") "local"
        importedKeyVerifiedVia := jStr (relayedRows[0]!) "keyVerifiedVia" }

      -- Credentials, on the node where they are the only way in.
      let claimD := claimOf "Foo.d" "00000000000000e5" "2024-04-01T00:00:00Z"
      let noCredential ← request p2 "POST" "/api/certificates" (publishBody claimD)
      let bogus ← request p2 "POST" "/api/certificates" (publishBody claimD)
        #[("Authorization", "Bearer trust_not-a-real-token")]
      let withToken ← request p2 "POST" "/api/certificates" (publishBody claimD)
        #[("Authorization", s!"Bearer {bobToken}")]
      let tokens ← request p2 "GET" "/api/tokens" "" #[("Authorization", s!"Bearer {bobToken}")]
      f := { f with
        publishWithoutCredentialStatus := noCredential.status
        publishWithBogusTokenStatus := bogus.status
        publishWithTokenAssurance := jStr (parsed withToken) "assurance"
        tokenListedCount := (jArr (parsed tokens) "tokens").size
        tokenSecretWithheld := !contains tokens.body bobToken }

      -- The cookie session: a row, looked up, and gone once it is logged out.
      let claimE := claimOf "Foo.e" "00000000000000f6" "2024-04-02T00:00:00Z"
      let withCookie ← request p2 "POST" "/api/certificates" (publishBody claimE)
        #[("Cookie", s!"trust_session={bobCookie}")]
      let _ ← request p2 "POST" "/auth/logout" "" #[("Cookie", s!"trust_session={bobCookie}")]
      let afterLogout ← request p2 "POST" "/api/certificates" (publishBody claimE)
        #[("Cookie", s!"trust_session={bobCookie}")]
      let expired ← request p2 "POST" "/api/certificates" (publishBody claimE)
        #[("Cookie", s!"trust_session={staleCookie}")]
      f := { f with
        cookieAssurance := jStr (parsed withCookie) "assurance"
        afterLogoutStatus := afterLogout.status
        expiredCookieStatus := expired.status }

      -- The trust list, and what it makes trusted.
      let followed ← request p1 "POST" s!"/api/trust-keys/{alice.primary}"
        (Json.compress (Json.mkObj [("label", Json.str "my laptop key")]))
      let notAFingerprint ← request p1 "POST" "/api/trust-keys/nonsense" ""
      let noSuchPerson ← request p1 "POST" "/api/trust-list/nobody" ""
      let list ← request p1 "GET" "/api/trust-list"
      let trusted ← request p1 "GET" "/api/trusted?hasher=semantic_hash/1"
      f := { f with
        trustKeysCount := if followed.status == 200 then (jArr (parsed list) "keys").size else 0
        trustedHashCount := (jArr (parsed trusted) "hashes").size
        badFingerprintStatus := notAFingerprint.status
        unknownLoginStatus := noSuchPerson.status }

      let missing ← request p1 "GET" "/api/nothing-here"
      let wrongMethod ← request p1 "GET" "/api/import"
      f := { f with
        unknownPathStatus := missing.status, wrongMethodStatus := wrongMethod.status }

      one.shutdownAndWait
      two.shutdownAndWait
      return { f with shutDownCleanly := true }

/-! ### The assertions -/

private def routeTests (f : RouteFindings) : TestSeq :=
  if !f.gpgAvailable then
    group "the routes" (test "SKIPPED: gpg is not on PATH, so nothing could be signed" true)
  else
  group "the routes" <|
    group "the node describes itself" (
      test "/api/health is well" (f.healthOk = true) <|
      test "and says which node it is" (f.healthName = "alice") <|
      test "§2's descriptor names this node's own external URL"
        (f.descriptorUrl = "http://one.test") <|
      test "and the protocol version it speaks" (f.descriptorProtocol = "trust/1") <|
      test "§9: a local node has an identity without anyone signing in"
        (f.meLogin = "alice") <|
      test "and says it is local, rather than sending the page looking for OAuth"
        (f.meLocal = true)) <|
    group "keys" (
      test "a public key registers under its own fingerprint"
        (f.keyFingerprint.length = 40) <|
      test "and is `self` until GitHub says otherwise" (f.keyVerifiedVia = "self") <|
      test "a private key is refused" (f.privateKeyStatus = 400) <|
      test "and told what it actually was"
        (contains f.privateKeyError "private key" = true) <|
      test "a key can be found by fingerprint, which is how a federated entry names one"
        (f.keyLookedUp = "alice")) <|
    group "publishing" (
      test "a signed certificate is accepted" (f.publishSignedStatus = 200) <|
      test "and is `signed`" (f.publishSignedAssurance = "signed") <|
      test "it comes back" (f.readBackCount = 1) <|
      -- The whole point of returning `canonical`: a reader never has to
      -- reconstruct what was signed in order to check it.
      test "with exactly the bytes that were signed"
        (f.readBackCanonical = f.expectedCanonical) <|
      test "labelled `signed`" (f.readBackAssurance = "signed") <|
      -- gpg signs with the *subkey*; §3.4 rule 5 says the entry names the
      -- primary, and this is the equality that pins the difference.
      test "attributed to the primary key, not the subkey that signed"
        (f.readBackFingerprint = f.expectedFingerprint) <|
      test "carrying the key, so the check can be repeated" (f.readBackKeyPresent = true) <|
      test "and saying this node checked it" (f.readBackVerifiedHere = true) <|
      test "a signature over other bytes is refused" (f.badSignatureStatus = 400) <|
      test "and the reason says so"
        (contains f.badSignatureError "signature did not verify" = true) <|
      test "an unsigned certificate is `attested`" (f.attestedAssurance = "attested") <|
      test "and is stored, and readable" (f.attestedVisible = 1)) <|
    group "§4.1 export" (
      test "a signed entry is exported" (f.exportSignedPresent = true) <|
      -- §3.1.  This is the line the whole assurance distinction exists to draw.
      test "an attested one is not, and must never be" (f.exportAttestedPresent = false) <|
      test "and §4.4's hints travel with the entry" (f.exportEntryHasHints = true)) <|
    group "§6 revocation" (
      test "a signed withdrawal is accepted from anyone" (f.revocationStatus = 200) <|
      test "and the bytes it was checked against come back"
        (f.revocationCanonical = f.expectedRevocationCanonical) <|
      test "the certificate it names disappears" (f.visibleAfterRevocation = 0) <|
      test "re-issuing afterwards reinstates, with no second message"
        (f.visibleAfterReissue = 1) <|
      test "a withdrawal signed by another key is refused" (f.forgedRevocationStatus = 400) <|
      test "because a revocation must be signed by the key it withdraws"
        (contains f.forgedRevocationError "but the key it travels with is" = true)) <|
    group "§4.3 paging" (
      test "there was more than one page of entries to walk" (f.pagedTotal > 2) <|
      test "the walk saw every one of them" (f.pagedSeen = f.pagedTotal) <|
      test "and none of them twice" (f.pagedNoRepeats = true) <|
      test "it really did take several pages" (f.pagedPages > 2) <|
      -- Honest truncation.  A receiver that mistakes truncation for exhaustion
      -- silently stops syncing, which is the failure nobody notices.
      test "the first page admits it was cut short" (f.firstPageComplete = false) <|
      test "and the last one says it is complete" (f.lastPageComplete = true)) <|
    group "§4.2 import" (
      test "a stranger cannot push a bundle at a public node"
        (f.importUnauthenticatedStatus = 403) <|
      test "the operator can, and the good entries are kept" (f.importAccepted > 0) <|
      test "the tampered one is not" (f.importRejected = 1) <|
      test "and its rejection is reported rather than swallowed" (f.importReasons = 1) <|
      test "with a reason in the sender's terms"
        (contains f.importReason "verify" = true || contains f.importReason "signature" = true) <|
      test "§2: a bundle in another protocol version is refused"
        (f.importedProtocolStatus = 400) <|
      test "an imported entry is readable on the receiving node" (f.importedVisible = 1) <|
      test "still `signed`, because the signature travelled with it"
        (f.importedAssurance = "signed") <|
      test "marked as not local" (f.importedLocal = false) <|
      test "and its key tied to nothing this node checked (§4.4)"
        (f.importedKeyVerifiedVia = "remote")) <|
    group "sessions without a MAC" (
      test "a public node refuses an unauthenticated publish"
        (f.publishWithoutCredentialStatus = 401) <|
      test "and a token that names no row" (f.publishWithBogusTokenStatus = 401) <|
      test "a command-line token authenticates" (f.publishWithTokenAssurance = "attested") <|
      test "tokens are listed" (f.tokenListedCount = 1) <|
      test "and never handed back" (f.tokenSecretWithheld = true) <|
      test "a cookie session authenticates" (f.cookieAssurance = "attested") <|
      test "logging out deletes the row, so the cookie stops meaning anything"
        (f.afterLogoutStatus = 401) <|
      test "and an expired session is refused" (f.expiredCookieStatus = 401)) <|
    group "trust lists" (
      test "a key can be followed" (f.trustKeysCount = 1) <|
      test "and what it vouches for becomes trusted" (f.trustedHashCount > 0) <|
      test "something that is not a fingerprint is refused" (f.badFingerprintStatus = 400) <|
      test "and following nobody says so" (f.unknownLoginStatus = 404)) <|
    group "the router" (
      test "an unknown path is a 404" (f.unknownPathStatus = 404) <|
      -- More useful than "not found" to somebody who has got the verb wrong.
      test "a known path under the wrong method is a 405" (f.wrongMethodStatus = 405) <|
      test "and both nodes shut down rather than hanging" (f.shutDownCleanly = true))

/-! ## Federation

Real nodes, on real sockets, in one process.

Federation is the part of this server that is *about* the other end being
somebody else, so the peer here is a second node with its own store, its own
port and its own opinion of the world, and the entries that travel between them
carry signatures a real `gpg` really made — by a signing subkey, so that §3.4
rule 5 is exercised across the wire and not only in the route tests.  What is
left to arrange is only what a test is entitled to arrange: which limits each
node enforces, and which of them is unreachable.
-/

/-- The `i`th hash this group asserts about: lower-case hex, as §3.4 rule 1 wants. -/
private def hashN (i : Nat) : String := s!"abcdef0123456789abcdef012345678{i}"

/-- An entry as it federates: signed over exactly `Claim.canonical`, key and all. -/
private def signedEntry (home : System.FilePath) (uid : String) (key : TestKey)
    (hash asserted : String) : IO Trust.Entry := do
  let claim := claimOf "Foo.bar" hash asserted "he said \"fine\", then\na newline"
  let signature ← signWith home uid claim.canonical
  return { claim, signature, key := key.armoredPublic, fingerprint := key.primary }

private structure Node where
  url : String
  store : Store
  app : IO.Ref App
  server : Server

/--
A node, listening.

The app goes in a ref because a node cannot be finished before it is bound: it
does not know its own URL until the OS has picked a port, and §5.2 and §7.1 both
turn on a node knowing its own URL.  `callsItself` is how a test builds one that
knows it wrongly.
-/
private def startNode (root : System.FilePath) (name : String) (policy : Policy)
    (routes : Array Route) (adminToken : String := "") (callsItself : String := "") :
    Async Node := do
  let store ← Store.open (root / name) { fsync := false }
  let config : ServerConfig := { port := 0, name, localMode := true, adminToken, policy }
  let app ← IO.mkRef ({ config, store } : App)
  let server ← serveRoutes config app routes
  let url := s!"http://127.0.0.1:{portOf server}"
  app.set { config := { config with
    publicUrl := if callsItself.isEmpty then url else callsItself }, store }
  return { url, store, app, server }

/-- A node from another protocol generation: honest, and unintelligible (§2). -/
private def foreignDescriptorRoute : Route where
  method := .get
  path := "/api/federation"
  run app _ := json Response.ok <| Json.mkObj [
    ("protocol", Json.str "trust/2"),
    ("url", Json.str (Federation.Service.ourUrl app)),
    ("name", Json.str "from the future")]

/--
A socket that accepts and never answers.

Not a slow route on a real node: a handler that slept would still be this
process's to schedule, and what §7.2 is about is a peer whose behaviour is not
ours at all.  Nothing ever calls `accept`, so the connection completes in the
kernel and the request waits for as long as the client will let it.
-/
private def blackHole : IO (TCP.Socket.Server × Nat) := do
  let socket ← TCP.Socket.Server.mk
  socket.bind (SocketAddress.v4 { addr := IPv4Addr.ofParts 127 0 0 1, port := 0 })
  socket.listen 8
  let port := match ← socket.getSockName with
    | .v4 a => a.port.toNat
    | .v6 a => a.port.toNat
  return (socket, port)

private structure FederationFindings where
  skipped : Bool := false
  /-- §5.2 -/
  announcedLiarStatus : Nat := 0
  announcedLiarError : String := ""
  liarRecorded : Bool := false
  announcedForeignStatus : Nat := 0
  announcedForeignError : String := ""
  foreignRecorded : Bool := false
  announcedPeerStatus : String := ""
  peerIsCandidate : Bool := false
  candidateIsNotQueried : Bool := false
  peersAfterSecondAnnounce : Nat := 0
  /-- §5.1, §5.3 -/
  promotionUnauthorized : Nat := 0
  promotionStatus : String := ""
  peersListed : String := ""
  /-- §4.1 → §4.2 -/
  pullAccepted : Nat := 0
  pullRejected : Nat := 0
  pullRounds : Nat := 0
  pullCursor : String := ""
  storedAfterPull : Nat := 0
  missingAfterPull : Nat := 0
  secondPullAccepted : Nat := 0
  secondPullRounds : Nat := 0
  cursorHeldStill : Bool := false
  /-- §7.3 -/
  cacheHitAsked : Nat := 0
  cacheHitFound : Nat := 0
  /-- §7 -/
  relayAsked : Nat := 0
  relayFound : Nat := 0
  relayFromPeer : String := ""
  peerUrl : String := ""
  relayIsLocal : Bool := true
  relayTruncated : Bool := true
  relayFetchedAt : Nat := 0
  cachedAsked : Nat := 0
  cachedFound : Nat := 0
  /-- §7.1 -/
  selfInViaAsked : Nat := 0
  selfInViaFound : Nat := 0
  peerInViaAsked : Nat := 0
  depthZeroAsked : Nat := 0
  clampedAsked : Nat := 0
  withoutViaAsked : Nat := 0
  withoutViaFound : Nat := 0
  /-- §7.4 -/
  httpAnswerStatus : Nat := 0
  httpAnswerBody : String := ""
  /-- §7.2 -/
  budgetMs : Nat := 0
  budgetAsked : Nat := 0
  budgetTruncated : Bool := false
  budgetFound : Nat := 0
  stillListening : Bool := false
  deriving Inhabited

private def runFederation (root : System.FilePath) : IO FederationFindings := do
  if !(← Trust.defaultVerifier.available) then
    return { skipped := true }
  IO.FS.withTempDir fun home => do
    let key ← makeKey home "Node Federation <node@example.org>"
    if key.primary.isEmpty then
      return { skipped := true }
    let mut entries := #[]
    for i in [0:9] do
      entries := entries.push
        (← signedEntry home "node@example.org" key (hashN i) s!"2024-01-0{i + 1}T00:00:00Z")
    let hinted (entry : Trust.Entry) (origin : String) : StoredCertificate :=
      { entry, hints := { issuer := "alice", keyVerifiedVia := "github", origin } }
    let quiet : Policy := { allowPrivate := true }
    Async.block do
      -- The peer.  Its own `maxEntries` is the default; what makes it truncate
      -- is the limit its reader asks for, which is that reader's §8 policy.
      let peer ← startNode root "peer" quiet
        (Federation.federationRoutes ++ Federation.peerRoutes)
      -- The node under test.  Three entries to a bundle, so seven of them
      -- cannot arrive in one.
      let node ← startNode root "node"
        { quiet with maxEntries := 3, peerTimeoutMs := 4000 }
        (Federation.federationRoutes ++ Federation.peerRoutes) (adminToken := "s3cret")
      let liar ← startNode root "liar" quiet Federation.federationRoutes
        (callsItself := "https://elsewhere.example")
      let foreign ← startNode root "foreign" quiet #[foreignDescriptorRoute]
      let port := portOf node.server
      for i in [0:7] do
        let _ ← peer.store.putCertificate (hinted entries[i]! peer.url)

      -- §5.2.  A node that calls itself something else cannot be announced,
      -- which is what stops this endpoint being pointed at a third party.
      let announceOf (url : String) : Async Reply :=
        request port "POST" "/api/peers/announce"
          (Json.compress (Json.mkObj [("url", Json.str url)]))
      let announcedLiar ← announceOf liar.url
      let liarRecorded := (← node.store.getPeer liar.url).isSome
        || (← node.store.getPeer "https://elsewhere.example").isSome
      let announcedForeign ← announceOf foreign.url
      let foreignRecorded := (← node.store.getPeer foreign.url).isSome
      -- §5.1: discovery proposes a candidate, and a candidate is never queried.
      let announcedPeer ← announceOf peer.url
      let peerIsCandidate :=
        ((← node.store.getPeer peer.url).map (·.status == .candidate)).getD false
      let candidateIsNotQueried := (← node.store.queriedPeers).isEmpty
      -- The same node announced by a URL written differently is the same node.
      let _ ← announceOf (peer.url ++ "/")
      let peersAfterSecondAnnounce := (← node.store.listPeers).size

      -- §5.1: only the operator promotes, and only with the operator's token.
      let promoting := Json.compress (Json.mkObj [("url", Json.str peer.url)])
      let refused ← request port "POST" "/api/peers/status/seed" promoting
      let promoted ← request port "POST" "/api/peers/status/seed" promoting
        #[("Authorization", "Bearer s3cret")]
      node.store.putPeer { url := "https://candidate.example", name := "c", status := .candidate }
      node.store.putPeer { url := "https://blocked.example", name := "b", status := .blocked }
      let peersListed ← request port "GET" "/api/peers"

      -- §4.1 → §4.2.  Seven entries, three to a bundle: `complete: false` means
      -- resume from the cursor, and nothing may be lost between the pages.
      let pull ← Federation.Service.detached
        (Federation.Service.pullFrom (← node.app.get) peer.url)
      let storedAfterPull := (← node.store.certificatesSince "" 1000).values.size
      let mut missingAfterPull := 0
      for i in [0:7] do
        if (← node.store.getCertificate key.primary (hashN i) "semantic_hash/1").isNone then
          missingAfterPull := missingAfterPull + 1
      let secondPull ← Federation.Service.detached
        (Federation.Service.pullFrom (← node.app.get) peer.url)
      let cursorHeldStill := secondPull.cursor == pull.cursor && !pull.cursor.isEmpty

      -- §7.3: what a pull left behind is the cache, and it answers without asking.
      let cacheHit ← Federation.Service.answer (← node.app.get)
        { hash := hashN 0, hasher := "semantic_hash/1", depth := 2 }

      -- Two entries the peer has and this node has not heard of.
      let _ ← peer.store.putCertificate (hinted entries[7]! peer.url)
      let _ ← peer.store.putCertificate (hinted entries[8]! peer.url)

      -- §7: a question this node cannot answer alone travels one hop.
      let relay ← Federation.Service.answer (← node.app.get)
        { hash := hashN 7, hasher := "semantic_hash/1", depth := 1 }
      let cached ← Federation.Service.answer (← node.app.get)
        { hash := hashN 7, hasher := "semantic_hash/1", depth := 1 }

      -- §7.1.  None of these four may reach the peer, and the peer is the only
      -- node that has `hashN 8`, so an answer with anything in it is a failure.
      let unheard : Federation.Service.Question :=
        { hash := hashN 8, hasher := "semantic_hash/1", depth := 2 }
      let selfInVia ← Federation.Service.answer (← node.app.get)
        { unheard with via := #[node.url] }
      let peerInVia ← Federation.Service.answer (← node.app.get)
        { unheard with via := #[peer.url] }
      let depthZero ← Federation.Service.answer (← node.app.get) { unheard with depth := 0 }
      let app ← node.app.get
      let clampedApp : App :=
        { app with config := { app.config with
            policy := { app.config.policy with maxDepth := 0 } } }
      let clamped ← Federation.Service.answer clampedApp { unheard with depth := 5 }
      -- …and with nothing in the way, the same question does travel.
      let withoutVia ← Federation.Service.answer (← node.app.get) unheard
      let httpAnswer ← request port "GET"
        s!"/api/certificates?hash={hashN 0}&hasher=semantic_hash/1&depth=0"

      -- §7.2.  One peer that never answers, a budget well inside its timeout,
      -- and a reader who is told the answer was cut short rather than that it
      -- is all there is.
      let (hole, holePort) ← blackHole
      let silent ← Store.open (root / "silent") { fsync := false }
      silent.putPeer { url := s!"http://127.0.0.1:{holePort}", status := .seed }
      let silentApp : App := {
        config := {
          port := 0, name := "silent", localMode := true
          publicUrl := "http://127.0.0.1:1"
          policy := { quiet with queryBudgetMs := 700, peerTimeoutMs := 3000 } }
        store := silent }
      let started ← nowMs
      let budget ← Federation.Service.answer silentApp
        { hash := hashN 0, hasher := "semantic_hash/1", depth := 1 }
      let budgetMs := (← nowMs) - started
      -- The socket has to be *used* after the measurement, or it is collected
      -- while the question is in flight and the port closes: a connection
      -- refused in a millisecond is not the peer §7.2 is about, and a test that
      -- measured one would pass for the wrong reason.
      let stillListening ← match ← hole.getSockName with
        | .v4 a => pure (a.port.toNat == holePort)
        | .v6 a => pure (a.port.toNat == holePort)

      node.server.shutdownAndWait
      peer.server.shutdownAndWait
      liar.server.shutdownAndWait
      foreign.server.shutdownAndWait
      return {
        announcedLiarStatus := announcedLiar.status
        announcedLiarError := jStr (parsed announcedLiar) "error"
        liarRecorded
        announcedForeignStatus := announcedForeign.status
        announcedForeignError := jStr (parsed announcedForeign) "error"
        foreignRecorded
        announcedPeerStatus := jStr (parsed announcedPeer) "status"
        peerIsCandidate, candidateIsNotQueried, peersAfterSecondAnnounce
        promotionUnauthorized := refused.status
        promotionStatus := jStr (parsed promoted) "status"
        peersListed := peersListed.body
        pullAccepted := pull.accepted, pullRejected := pull.rejected, pullRounds := pull.rounds
        pullCursor := pull.cursor, storedAfterPull, missingAfterPull
        secondPullAccepted := secondPull.accepted, secondPullRounds := secondPull.rounds
        cursorHeldStill
        cacheHitAsked := cacheHit.askedPeers, cacheHitFound := cacheHit.certificates.size
        relayAsked := relay.askedPeers, relayFound := relay.certificates.size
        relayFromPeer := ((relay.certificates[0]?).map (·.fromPeer)).getD "<nothing>"
        peerUrl := peer.url
        relayIsLocal := ((relay.certificates[0]?).map (·.fromPeer.isEmpty)).getD true
        relayTruncated := relay.truncated
        relayFetchedAt := ((relay.certificates[0]?).map (·.fetchedMs)).getD 0
        cachedAsked := cached.askedPeers, cachedFound := cached.certificates.size
        selfInViaAsked := selfInVia.askedPeers, selfInViaFound := selfInVia.certificates.size
        peerInViaAsked := peerInVia.askedPeers
        depthZeroAsked := depthZero.askedPeers
        clampedAsked := clamped.askedPeers
        withoutViaAsked := withoutVia.askedPeers, withoutViaFound := withoutVia.certificates.size
        httpAnswerStatus := httpAnswer.status, httpAnswerBody := httpAnswer.body
        budgetMs, budgetAsked := budget.askedPeers, budgetTruncated := budget.truncated
        budgetFound := budget.certificates.size, stillListening }

private def federationTests (f : FederationFindings) : TestSeq :=
  if f.skipped then
    group "federation" <|
      test "SKIPPED: gpg is not on PATH, so no signed entry could be made" true
  else
  group "federation" <|
    group "§5.2 announcing" (
      test "a node that calls itself something else is refused"
        (contains f.announcedLiarError "calls itself something else" = true) <|
      test "with a 400 rather than a silence" (f.announcedLiarStatus = 400) <|
      test "and is not recorded under either name, which is what stops a scanner"
        (f.liarRecorded = false) <|
      test "a node speaking another protocol is refused"
        (contains f.announcedForeignError "speaks trust/2" = true) <|
      test "also with a 400" (f.announcedForeignStatus = 400) <|
      test "and is not recorded" (f.foreignRecorded = false) <|
      test "a node that names itself correctly is recorded"
        (f.announcedPeerStatus = "candidate") <|
      test "as a candidate, because autodiscover is off" (f.peerIsCandidate = true) <|
      test "and a candidate is never queried" (f.candidateIsNotQueried = true) <|
      test "the same node announced by a differently written URL is the same node"
        (f.peersAfterSecondAnnounce = 1)) <|
    group "§5.1 and §5.3 peer states" (
      test "promotion needs the operator's token" (f.promotionUnauthorized = 401) <|
      test "and with it, moves the peer" (f.promotionStatus = "seed") <|
      test "§5.3 lists what this node queries" (contains f.peersListed "127.0.0.1" = true) <|
      test "and not a candidate, whose address this node was merely asked to probe"
        (contains f.peersListed "candidate.example" = false) <|
      test "and not a blocked node, which is the operator's judgement"
        (contains f.peersListed "blocked.example" = false)) <|
    group "§4.1 pulling from a peer that truncates" (
      test "every entry arrived" (f.pullAccepted = 7) <|
      test "and none was refused" (f.pullRejected = 0) <|
      test "it took more than one bundle, so `complete: false` really was resumed"
        (f.pullRounds = 3) <|
      test "the store holds them all" (f.storedAfterPull = 7) <|
      test "and nothing fell between two pages" (f.missingAfterPull = 0) <|
      test "the cursor was kept" (f.pullCursor ≠ "") <|
      test "a second pull from the same cursor accepts nothing"
        (f.secondPullAccepted = 0) <|
      test "in one round" (f.secondPullRounds = 1) <|
      test "and leaves the cursor where it was" (f.cursorHeldStill = true)) <|
    group "§7.3 the cache" (
      test "a fresh remote answer is answered from here" (f.cacheHitAsked = 0) <|
      test "and it is the entry that was pulled" (f.cacheHitFound = 1) <|
      test "a question nobody here can answer goes out" (f.relayAsked = 1) <|
      test "and comes back with the certificate" (f.relayFound = 1) <|
      test "marked as somebody else's" (f.relayIsLocal = false) <|
      test "with the peer it came from" (f.relayFromPeer = f.peerUrl) <|
      test "and when it arrived" (f.relayFetchedAt > 0) <|
      test "the answer is not truncated: everyone asked, answered"
        (f.relayTruncated = false) <|
      test "asking again within the TTL asks nobody" (f.cachedAsked = 0) <|
      test "and answers anyway" (f.cachedFound = 1)) <|
    group "§7.1 depth and loops" (
      test "a node that finds itself in `via` relays nowhere" (f.selfInViaAsked = 0) <|
      test "and answers locally, which here is with nothing" (f.selfInViaFound = 0) <|
      test "a peer already in `via` is not relayed to" (f.peerInViaAsked = 0) <|
      test "depth 0 is local only" (f.depthZeroAsked = 0) <|
      test "and the asker's depth is clamped to this node's own maximum"
        (f.clampedAsked = 0) <|
      test "with nothing in the way, the same question does travel"
        (f.withoutViaAsked = 1) <|
      test "and is answered" (f.withoutViaFound = 1)) <|
    group "§7.4 the response" (
      test "§7 answers over HTTP" (f.httpAnswerStatus = 200) <|
      test "with the canonical bytes, so the reader need not rebuild them"
        (contains f.httpAnswerBody "\"canonical\":\"{\\\"asserted\\\"" = true) <|
      test "saying this node checked it"
        (contains f.httpAnswerBody "\"verifiedHere\":true" = true) <|
      test "that hints are not to be believed"
        (contains f.httpAnswerBody "\"hintsVerified\":false" = true) <|
      test "and that the answer is whole"
        (contains f.httpAnswerBody "\"truncated\":false" = true)) <|
    group "§7.2 the budget" (
      test "a peer that never answers is asked" (f.budgetAsked = 1) <|
      test "and really was listening, rather than refusing in a millisecond"
        (f.stillListening = true) <|
      test "and waited for, but only until the budget expires"
        (f.budgetMs ≥ 700 ∧ f.budgetMs < 2500) <|
      test "the answer says it was cut short" (f.budgetTruncated = true) <|
      test "rather than reporting that nobody vouches for it" (f.budgetFound = 0))

/-! ## Runner -/

def main : IO UInt32 := do
  let root ← IO.FS.createTempDir
  try
    let findings ← runStore root
    let routes ← runRoutes root
    let federated ← runFederation root
    lspecIO (.ofList [
      ("timestamps", [timeTests]),
      ("config", [configTests]),
      ("store", [storeTests findings]),
      ("routes", [routeTests routes]),
      ("federation", [federationTests federated])]) []
  finally
    IO.FS.removeDirAll root
