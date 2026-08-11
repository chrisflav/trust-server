import LSpec
import TrustServer

/-!
# Tests

Everything here runs against a real directory on disk and, for the last group, a
real socket.  The store's whole premise is that its state is a file, so a test
that mocked the file would be testing something else.

The IO happens first and the assertions are made afterwards about what it
produced, because `LSpec.TestSeq` is a pure value: a failure then reports the
state the store was actually in rather than an exception from inside a test
description.
-/

open LSpec
open Std Std.Http Std.Async Std.Net
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

/-! ## The server -/

/-- A raw HTTP/1.1 GET: Lean has no HTTP client, and curl is not a dependency. -/
private def httpGet (port : Nat) (path : String) : Async String := do
  let client ← TCP.Socket.Client.mk
  client.connect (SocketAddress.v4 {
    addr := IPv4Addr.ofParts 127 0 0 1, port := UInt16.ofNat port })
  let request :=
    s!"GET {path} HTTP/1.1\r\nHost: 127.0.0.1\r\nConnection: close\r\n\r\n"
  client.send request.toUTF8
  let mut out := ByteArray.empty
  repeat
    match ← client.recv? 4096 with
    | some chunk => if chunk.isEmpty then break else out := out ++ chunk
    | none => break
  return String.fromUTF8! out

private structure ServerFindings where
  port : Nat
  health : String
  missing : String
  shutDownCleanly : Bool

private def runServerChecks (root : System.FilePath) : IO ServerFindings := do
  let store ← Store.open (root / "served") { fsync := false }
  let _ ← store.putCertificate (certOf fpA hash1 "2024-01-01T00:00:00Z")
  store.putPeer { url := "https://seed.example", status := .seed }
  -- Port 0: the OS picks a free one and `localAddr` says which, so the test
  -- never races another process for a fixed number.
  let config : ServerConfig := { port := 0, name := "test-node", localMode := true }
  Async.block do
    let server ← TrustServer.serve config store
    let port := boundPort server
    let health ← httpGet port "/api/health"
    let missing ← httpGet port "/api/nothing-here"
    server.shutdownAndWait
    return { port, health, missing, shutDownCleanly := true }

private def contains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

private def serverTests (f : ServerFindings) : TestSeq :=
  group "the server skeleton" <|
    test "it bound to a port" (f.port > 0) <|
    test "/api/health answers 200" (contains f.health "200 OK" = true) <|
    test "as JSON" (contains f.health "application/json" = true) <|
    test "saying it is well" (contains f.health "\"ok\":true" = true) <|
    test "and reporting what the store actually holds"
      (contains f.health "\"certificates\":1" = true) <|
    test "and which peers it queries" (contains f.health "\"peers\":1" = true) <|
    test "anything else is a 404" (contains f.missing "404" = true) <|
    test "and it shuts down rather than hanging" (f.shutDownCleanly = true)

/-! ## Runner -/

def main : IO UInt32 := do
  let root ← IO.FS.createTempDir
  try
    let findings ← runStore root
    let served ← runServerChecks root
    lspecIO (.ofList [
      ("timestamps", [timeTests]),
      ("config", [configTests]),
      ("store", [storeTests findings]),
      ("server", [serverTests served])]) []
  finally
    IO.FS.removeDirAll root
