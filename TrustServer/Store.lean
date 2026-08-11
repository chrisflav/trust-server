import Lean
import Std.Data.HashMap
import Std.Sync.Mutex
import Std.Time
import Trust.Cert

/-!
# The store: an append-only log on disk, an index in memory

## Why a log and not SQLite

The obvious thing would have been SQLite, and it is not what this does.

`leansqlite` is the only binding worth using, and it needs a C toolchain at
build time — which every machine that wants to run a node would then need too —
and, more decisively, it pins `leanprover/lean4:v4.34.0-rc1`.  Following that
pin would mean bumping this package's toolchain, and bumping the toolchain moves
the pinned `semantic_hash` revision that certificate hashes are computed with.
A certificate is only worth anything if the hash it names can be recomputed, so
moving that revision would silently change what every hash in the database
means.  A storage engine is not worth that.

So the store is a directory of append-only JSONL files, one per table, read
into `Std.HashMap` on startup.  Everything the protocol needs from a database it
gets here:

* **§4.3's cursor.**  Every record carries `seq`, a row id unique across the
  whole store, and `updatedAt` in epoch milliseconds.  The cursor
  `<epoch-ms>.<row-id>` *is* the pair `(updatedAt, seq)`, and because `seq` is
  unique the order it induces is total — two rows written in the same
  millisecond still have a definite order, which is exactly the case a plain
  timestamp cursor loses.
* **Updates and deletes.**  A later record for the same key supersedes an
  earlier one; a delete appends a record with no value.  Nothing is ever
  rewritten in place, so a resuming peer sees the change rather than missing it.
* **§3.5 and §6.2.**  Both are decided here, in `putCertificate` and
  `isRevoked`, rather than by whoever happens to call the store.

## Durability

Every write is `putStr`, then `flush`, then — when `Options.fsync` is set —
`fdatasync`, before the in-memory index is touched and before the call returns.

`flush` pushes the C stdio buffer into the kernel.  Getting from there onto the
disk needs `fsync(2)`, and **Lean v4.32.0 exposes no `fsync` or `fdatasync` on
`IO.FS.Handle`** — there is no such function anywhere in the toolchain's sources.
A pure-Lean store therefore cannot call it directly, so `syncPath` shells out to
coreutils' `sync --data`, which is `fdatasync` on the named file.  That is a
subprocess per write, which is why it is a flag; `Options.fsync := false` gives
`flush` only, which survives this process dying but not the machine dying.
-/

namespace TrustServer

open Lean (Json ToJson FromJson toJson fromJson?)
open System (FilePath)

/-! ## Time -/

/-- The current time in epoch milliseconds, which is what a cursor is made of. -/
def nowMs : IO Nat := do
  let ts ← Std.Time.Timestamp.now
  return ts.toMillisecondsSinceUnixEpoch.val.toNat

/--
Days from 1970-01-01 to `y-m-d`, by Howard Hinnant's days-from-civil algorithm.

Written out rather than taken from `Std.Time` because the only thing needed is a
total order on the timestamps §3.5 and §6.2 compare, and a parser that returns
`none` on anything it does not understand is easier to reason about than one
that throws.
-/
private def daysFromCivil (y m d : Nat) : Int :=
  let y' := if m ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' - era * 400
  let mp := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  ((era * 146097 + doe : Nat) : Int) - (719468 : Nat)

private def takeDigits (cs : List Char) (n : Nat) : Option (Nat × List Char) := Id.run do
  let mut value := 0
  let mut rest := cs
  for _ in [0:n] do
    match rest with
    | c :: tail =>
      if c.isDigit then
        value := value * 10 + (c.val - '0'.val).toNat
        rest := tail
      else
        return none
    | [] => return none
  return some (value, rest)

/--
An RFC 3339 timestamp as epoch milliseconds, or `none` if it is not one.

Accepts `YYYY-MM-DDTHH:MM:SS`, optional fractional seconds, and either `Z` or a
numeric offset.  A missing zone is read as UTC: §3.2 says these are UTC, and
refusing to order a timestamp because it omitted the `Z` would be worse than
assuming what the specification already requires.
-/
def parseTimestampMs (s : String) : Option Int := do
  let cs := s.trimAscii.toString.toList
  let (year, cs) ← takeDigits cs 4
  let cs ← match cs with | '-' :: t => some t | _ => none
  let (month, cs) ← takeDigits cs 2
  let cs ← match cs with | '-' :: t => some t | _ => none
  let (day, cs) ← takeDigits cs 2
  if month < 1 || month > 12 || day < 1 || day > 31 then none
  let cs ← match cs with
    | c :: t => if c == 'T' || c == 't' || c == ' ' then some t else none
    | _ => none
  let (hour, cs) ← takeDigits cs 2
  let cs ← match cs with | ':' :: t => some t | _ => none
  let (minute, cs) ← takeDigits cs 2
  let cs ← match cs with | ':' :: t => some t | _ => none
  let (second, cs) ← takeDigits cs 2
  -- Fractional seconds, to millisecond precision; further digits are dropped
  -- rather than rounded, so that ordering never depends on how many a signer
  -- happened to write.
  let (millis, cs) :=
    match cs with
    | '.' :: rest =>
      let frac := rest.takeWhile Char.isDigit
      let tail := rest.dropWhile Char.isDigit
      let digits := frac.take 3 ++ List.replicate (3 - min 3 frac.length) '0'
      (digits.foldl (fun acc c => acc * 10 + (c.val - '0'.val).toNat) 0, tail)
    | _ => (0, cs)
  let offsetSeconds : Int ←
    match cs with
    | [] => some 0
    | ['Z'] | ['z'] => some 0
    | sign :: rest =>
      if sign != '+' && sign != '-' then none
      else do
        let (oh, rest) ← takeDigits rest 2
        let rest := match rest with | ':' :: t => t | t => t
        let (om, rest) ← takeDigits rest 2
        if !rest.isEmpty then none
        let magnitude : Int := oh * 3600 + om * 60
        some (if sign == '-' then -magnitude else magnitude)
  let days := daysFromCivil year month day
  let seconds := days * 86400 + (hour * 3600 + minute * 60 + second : Nat) - offsetSeconds
  some (seconds * 1000 + millis)

/--
Whether `a` is strictly later than `b`.

Both are timestamps as they were *signed*, so they are compared as instants when
both parse, and lexicographically when they do not — an unparseable timestamp
still has to sort somewhere, and RFC 3339 in UTC sorts correctly as text anyway.
Strictness is what §3.5 means by "ties keep what is already stored".
-/
def isLater (a b : String) : Bool :=
  match parseTimestampMs a, parseTimestampMs b with
  | some x, some y => x > y
  | _, _ => a > b

/-! ## Cursors (§4.3) -/

/--
A position in the log: the millisecond a row last changed, and the row id.

Opaque to a receiver, which stores the string and hands it back.  The row id is
what makes the order total, so that rows written in the same tick cannot be
skipped by a resume.
-/
structure Cursor where
  ms : Nat
  seq : Nat
  deriving Inhabited, Repr, DecidableEq

namespace Cursor

def encode (c : Cursor) : String := s!"{c.ms}.{c.seq}"

def decode? (s : String) : Option Cursor :=
  match s.splitOn "." with
  | [ms, seq] => do
    let ms ← ms.toNat?
    let seq ← seq.toNat?
    some { ms, seq }
  | _ => none

/-- Strictly after, in the total order the cursor names. -/
def after (c d : Cursor) : Bool := c.ms > d.ms || (c.ms == d.ms && c.seq > d.seq)

end Cursor

/-! ## Records -/

/--
One line of a log.

`value` is `none` for a tombstone, which is how a delete travels: a peer walking
the cursor sees the removal instead of quietly never hearing about it again.
-/
structure Row (α : Type) where
  seq : Nat
  updatedAt : Nat
  /-- The record's identity within its table. -/
  key : String
  value : Option α
  deriving Inhabited

def Row.cursor (r : Row α) : Cursor := { ms := r.updatedAt, seq := r.seq }

private def Row.render [ToJson α] (r : Row α) : Json :=
  Json.mkObj <|
    [("seq", toJson r.seq), ("updatedAt", toJson r.updatedAt), ("key", Json.str r.key)] ++
      match r.value with
      | some v => [("value", toJson v)]
      | none => [("deleted", Json.bool true)]

private def Row.parse? [FromJson α] (j : Json) : Except String (Row α) := do
  let seq ← j.getObjValAs? Nat "seq"
  let updatedAt ← j.getObjValAs? Nat "updatedAt"
  let key ← j.getObjValAs? String "key"
  let deleted := (j.getObjValAs? Bool "deleted").toOption.getD false
  let value ← if deleted then pure none else some <$> fromJson? (← j.getObjVal? "value")
  return { seq, updatedAt, key, value }

/-- What `putCertificate` decided. -/
inductive PutOutcome where
  /-- Nothing was stored under that triple before. -/
  | inserted
  /-- The arriving entry asserted later, so it replaced what was there. -/
  | replaced
  /-- What is stored asserted later, or exactly as late; §3.5 keeps it. -/
  | kept
  deriving Inhabited, Repr, DecidableEq, BEq

/-- A page of rows in cursor order, with where to resume and whether it was cut short. -/
structure Page (α : Type) where
  rows : Array (Row α)
  /-- Where a caller resumes.  Unchanged from what was asked for when nothing is new. -/
  cursor : String
  /-- True when the page stopped at `limit` rather than at the end. -/
  truncated : Bool
  deriving Inhabited

/-- The rows that still exist, tombstones dropped. -/
def Page.values (p : Page α) : Array α := p.rows.filterMap (·.value)

/-- §4's `complete`: false when the sender truncated, and it must be set honestly. -/
def Page.complete (p : Page α) : Bool := !p.truncated

/-! ## What the tables hold -/

/--
What the origin knows and a receiver cannot check (§4.4).

Stored for display and marked unverified wherever it is shown.  Nothing in this
file lets a hint affect acceptance or ordering.
-/
structure Hints where
  issuer : String := ""
  keyVerifiedVia : String := ""
  origin : String := ""
  deriving Inhabited, Repr, DecidableEq, ToJson, FromJson

/-- A federated entry as it is kept: §3.3's four fields, plus where it came from. -/
structure StoredCertificate where
  entry : Trust.Entry
  hints : Hints := {}
  /-- The peer it arrived from; empty when this node originated it. -/
  fromPeer : String := ""
  /-- When it arrived, epoch milliseconds; `0` for a local assertion. -/
  fetchedMs : Nat := 0
  deriving Inhabited

instance : ToJson StoredCertificate where
  toJson c := Json.mkObj [
    ("entry", toJson c.entry), ("hints", toJson c.hints),
    ("fromPeer", Json.str c.fromPeer), ("fetchedMs", toJson c.fetchedMs)]

instance : FromJson StoredCertificate where
  fromJson? j := do
    return {
      entry := ← fromJson? (← j.getObjVal? "entry")
      hints := (j.getObjVal? "hints" >>= fromJson?).toOption.getD {}
      fromPeer := (j.getObjValAs? String "fromPeer").toOption.getD ""
      fetchedMs := (j.getObjValAs? Nat "fetchedMs").toOption.getD 0 }

/-- The four states of §5.1.  Discovery may propose a candidate, never promote one. -/
inductive PeerStatus where
  /-- Configured by the operator; queried. -/
  | seed
  /-- Discovered and admitted by policy; queried. -/
  | active
  /-- Discovered, not admitted; recorded, never queried. -/
  | candidate
  /-- Never queried, never re-admitted by discovery. -/
  | blocked
  deriving Inhabited, Repr, DecidableEq, BEq

namespace PeerStatus

def toString : PeerStatus → String
  | .seed => "seed" | .active => "active" | .candidate => "candidate" | .blocked => "blocked"

def ofString? : String → Option PeerStatus
  | "seed" => some .seed | "active" => some .active
  | "candidate" => some .candidate | "blocked" => some .blocked
  | _ => none

/-- §5.3: a node lists only the peers it queries itself. -/
def queried : PeerStatus → Bool
  | .seed | .active => true
  | .candidate | .blocked => false

end PeerStatus

instance : ToJson PeerStatus where toJson s := Json.str s.toString
instance : FromJson PeerStatus where
  fromJson? j := do
    let s ← j.getStr?
    match PeerStatus.ofString? s with
    | some status => return status
    | none => throw s!"`{s}` is not a peer status"

structure Peer where
  url : String
  name : String := ""
  status : PeerStatus := .candidate
  /-- How far this node has read that peer's export (§4.1). -/
  cursor : String := ""
  lastSeenMs : Nat := 0
  lastError : String := ""
  addedMs : Nat := 0
  deriving Inhabited, Repr, ToJson, FromJson

/-- An account this node knows about.  Only a public key is ever stored beside it. -/
structure Identity where
  login : String
  githubId : Int := -1
  avatarUrl : String := ""
  createdMs : Nat := 0
  deriving Inhabited, Repr, ToJson, FromJson

/--
A command-line token, by its digest.

The token itself is never written down: a leaked store should not hand anyone
the ability to publish as someone else.  A token says who is publishing; it
cannot forge a signature, so it is not what makes a certificate worth anything.
-/
structure Session where
  tokenSha256 : String
  login : String
  name : String := ""
  createdMs : Nat := 0
  lastUsedMs : Nat := 0
  deriving Inhabited, Repr, ToJson, FromJson

/-- Whose certificates count for someone.  Explicit, one hop, never transitive. -/
structure Follow where
  truster : String
  /-- A key fingerprint when `kind` is `"key"`, a login when it is `"login"`. -/
  target : String
  kind : String := "key"
  label : String := ""
  addedMs : Nat := 0
  deriving Inhabited, Repr, ToJson, FromJson

/-! ## Keys -/

/--
An injective encoding of a tuple as one string.

Length-prefixed rather than joined with a separator: the parts are
attacker-supplied — an entry arrives over the network — and `a ++ "/" ++ b` is
only injective if you can promise no part contains a slash.
-/
def tupleKey (parts : List String) : String :=
  String.join (parts.map fun p => s!"{p.length}:{p}")

/-- §3.5: an entry's identity is `(fingerprint, hash, hasher)`, nothing else. -/
def certificateKey (fingerprint hash hasher : String) : String :=
  tupleKey [fingerprint.toLower, hash.toLower, hasher]

/-- §6.2 matches on the same triple, so a revocation is keyed the same way. -/
def revocationKey (fingerprint hash hasher : String) : String :=
  certificateKey fingerprint hash hasher

/-! ## Tables -/

/-- How durable a write has to be before it is allowed to return. -/
structure Options where
  /--
  Whether to `fdatasync` after every append.

  On, a write that returned survives the machine losing power.  Off, it survives
  only this process dying.  See the note at the top of this file: v4.32.0 has no
  `fsync` on `IO.FS.Handle`, so "on" costs a subprocess.
  -/
  fsync : Bool := true
  /-- Rewrite a log when it holds this many times more records than live rows. -/
  compactionRatio : Nat := 4
  deriving Inhabited

/-- `fdatasync` on a path, via coreutils.  See the durability note above. -/
private def syncPath (path : FilePath) : IO Unit := do
  let out ← IO.Process.output { cmd := "sync", args := #["--data", path.toString] }
  if out.exitCode != 0 then
    throw <| IO.userError s!"could not fdatasync {path}: {out.stderr.trimAscii}"

/--
One append-only file, plus the index built from it.

`live` maps a key to the newest row carrying it, tombstones included: a
tombstone is still the current state of that key, and dropping it would take the
delete off the cursor.
-/
structure Table (α : Type) where
  path : FilePath
  handle : IO.FS.Handle
  live : Std.HashMap String (Row α)
  /-- Rows in the file, superseded ones included.  Compaction watches this. -/
  total : Nat

namespace Table

/--
Read a table's file into memory.

A file that does not end in a newline was cut short by something that died
mid-append; the partial line is dropped and the file truncated to the last
complete one, because appending after it would splice two records into one.
-/
def load (path : FilePath) [FromJson α] : IO (Table α) := do
  let mut rows : Array (Row α) := #[]
  let mut total := 0
  if ← path.pathExists then
    let text ← IO.FS.readFile path
    let complete :=
      if text.isEmpty || text.endsWith "\n" then text
      else
        -- Everything up to the last newline; the trailing fragment is the
        -- record whoever died was in the middle of writing.
        match text.splitOn "\n" |>.dropLast with
        | [] => ""
        | lines => String.intercalate "\n" lines ++ "\n"
    if complete != text then
      IO.FS.writeFile path complete
    for line in complete.splitOn "\n" do
      if line.trimAscii.toString.isEmpty then continue
      match Json.parse line >>= Row.parse? with
      | .ok row => rows := rows.push row; total := total + 1
      | .error e => throw <| IO.userError s!"{path}: unreadable record: {e}"
  let handle ← IO.FS.Handle.mk path .append
  let mut live : Std.HashMap String (Row α) := {}
  for row in rows do
    -- Last write wins, by position in the log.
    live := live.insert row.key row
  return { path, handle, live, total }

/-- Append one row: to the file, to the disk, and only then to the index. -/
def append [ToJson α] (t : Table α) (opts : Options) (row : Row α) : IO (Table α) := do
  t.handle.putStr (Json.compress row.render ++ "\n")
  t.handle.flush
  if opts.fsync then syncPath t.path
  return { t with live := t.live.insert row.key row, total := t.total + 1 }

/-- The rows the index would rebuild from, in cursor order. -/
def liveRows (t : Table α) : Array (Row α) :=
  (t.live.toArray.map (·.2)).qsort fun a b => b.cursor.after a.cursor

/--
Rewrite the file with only the rows that still say something.

Through a temporary file and `rename`, so that a crash leaves either the old log
or the new one and never a half-written one.  Rows keep their `seq` and
`updatedAt`, so no peer's cursor is invalidated by compaction.
-/
def compact [ToJson α] (t : Table α) (opts : Options) : IO (Table α) := do
  let rows := t.liveRows
  let tmp := FilePath.mk (t.path.toString ++ ".compacting")
  let out ← IO.FS.Handle.mk tmp .write
  for row in rows do
    out.putStr (Json.compress row.render ++ "\n")
  out.flush
  if opts.fsync then syncPath tmp
  IO.FS.rename tmp t.path
  let handle ← IO.FS.Handle.mk t.path .append
  return { t with handle, total := rows.size }

/-- Rewrite only when the log has grown well past what it is saying. -/
def compactIfNeeded [ToJson α] (t : Table α) (opts : Options) : IO (Table α) := do
  if t.live.isEmpty then return t
  if t.total > opts.compactionRatio * t.live.size then t.compact opts else return t

/-- Rows strictly after `since`, in cursor order, at most `limit` of them. -/
def page (t : Table α) (since : Option Cursor) (limit : Nat) : Page α :=
  let ordered := t.liveRows.filter fun r =>
    match since with
    | some c => r.cursor.after c
    | none => true
  let truncated := ordered.size > limit
  let rows := ordered.extract 0 limit
  let cursor :=
    match rows.back?, since with
    | some last, _ => last.cursor.encode
    -- Nothing new: hand back what was asked for, so an idle peer does not walk
    -- back to the beginning of the log.
    | none, some c => c.encode
    | none, none => ""
  { rows, cursor, truncated }

end Table

/-! ## The store -/

/-- Everything the log holds, plus the counter the cursor's row ids come from. -/
structure StoreState where
  dir : FilePath
  opts : Options
  /-- Unique across the whole store, so that the cursor order is total. -/
  nextSeq : Nat
  certificates : Table StoredCertificate
  revocations : Table Trust.SignedRevocation
  peers : Table Peer
  identities : Table Identity
  sessions : Table Session
  follows : Table Follow

/--
A directory of append-only logs, behind one lock.

Every mutation goes through `Std.Mutex`, so two handlers cannot interleave an
append: the file would still be well-formed, but the `seq` counter would not be,
and a cursor built from a duplicated row id skips rows.
-/
structure Store where
  private state : Std.Mutex StoreState

namespace Store

private def maxSeq (rows : Array (Row α)) : Nat :=
  rows.foldl (fun acc r => max acc r.seq) 0

/-- Open (creating if need be) the store in `dir`, and index everything in it. -/
def «open» (dir : FilePath) (opts : Options := {}) : IO Store := do
  IO.FS.createDirAll dir
  let certificates ← Table.load (α := StoredCertificate) (dir / "certificates.jsonl")
  let revocations ← Table.load (α := Trust.SignedRevocation) (dir / "revocations.jsonl")
  let peers ← Table.load (α := Peer) (dir / "peers.jsonl")
  let identities ← Table.load (α := Identity) (dir / "identities.jsonl")
  let sessions ← Table.load (α := Session) (dir / "sessions.jsonl")
  let follows ← Table.load (α := Follow) (dir / "follows.jsonl")
  -- The next row id continues past everything already written; reusing one
  -- would make two rows share a cursor position, which is the one thing the
  -- row id exists to prevent.
  let nextSeq := 1 + max (maxSeq certificates.liveRows)
    (max (maxSeq revocations.liveRows) (max (maxSeq peers.liveRows)
      (max (maxSeq identities.liveRows) (max (maxSeq sessions.liveRows)
        (maxSeq follows.liveRows)))))
  let certificates ← certificates.compactIfNeeded opts
  let revocations ← revocations.compactIfNeeded opts
  let peers ← peers.compactIfNeeded opts
  let identities ← identities.compactIfNeeded opts
  let sessions ← sessions.compactIfNeeded opts
  let follows ← follows.compactIfNeeded opts
  let state ← Std.Mutex.new
    { dir, opts, nextSeq, certificates, revocations, peers, identities, sessions, follows }
  return { state }

/-- Read something out of the index under the lock. -/
private def read (s : Store) (f : StoreState → β) : IO β :=
  s.state.atomically do return f (← get)

/--
Append one row to one table.

The `seq` and `updatedAt` are taken here rather than by the caller, so that they
are allocated under the same lock that does the append: the cursor order can
then never disagree with the order the file is in.
-/
private def write [ToJson α] (s : Store)
    (peek : StoreState → Table α) (poke : StoreState → Table α → StoreState)
    (key : String) (value : Option α) : IO Cursor :=
  s.state.atomically do
    let st ← get
    let seq := st.nextSeq
    let updatedAt ← nowMs
    let table ← (peek st).append st.opts { seq, updatedAt, key, value }
    set (poke { st with nextSeq := seq + 1 } table)
    return { ms := updatedAt, seq }

/-! ### Certificates (§3.5) -/

/--
Store an entry, resolving §3.5's collision.

The identity is `(fingerprint, hash, hasher)`; hashes from different hashers are
never comparable, so the hasher is part of the key rather than an attribute.  On
collision the later `asserted` wins, and a tie keeps what is already stored —
which is what makes gossiping the same set repeatedly converge instead of
oscillating between two nodes' copies.
-/
def putCertificate (s : Store) (cert : StoredCertificate) : IO PutOutcome := do
  let claim := cert.entry.claim
  let key := certificateKey cert.entry.fingerprint claim.hash claim.hasher
  let existing ← s.read fun st => (st.certificates.live.get? key).bind (·.value)
  let outcome :=
    match existing with
    | none => PutOutcome.inserted
    | some old => if isLater claim.asserted old.entry.claim.asserted then .replaced else .kept
  if outcome == .kept then return outcome
  let _ ← s.write (·.certificates) (fun st t => { st with certificates := t }) key (some cert)
  return outcome

/-- Withdraw a certificate from this node's log by appending a tombstone. -/
def deleteCertificate (s : Store) (fingerprint hash hasher : String) : IO Unit := do
  let key := certificateKey fingerprint hash hasher
  let _ ← s.write (·.certificates) (fun st t => { st with certificates := t }) key none

def getCertificate (s : Store) (fingerprint hash hasher : String) :
    IO (Option StoredCertificate) :=
  s.read fun st =>
    (st.certificates.live.get? (certificateKey fingerprint hash hasher)).bind (·.value)

/-! ### Revocations (§6) -/

/--
Store a withdrawal.

Kept whether or not the certificate it names has ever been seen (§6, rule 4):
the certificate may arrive by another path afterwards, and dropping the
revocation would resolve that race in favour of the assertion.  A later
`revoked` for the same triple supersedes an earlier one.
-/
def putRevocation (s : Store) (rev : Trust.SignedRevocation) : IO PutOutcome := do
  let r := rev.revocation
  let key := revocationKey r.fingerprint r.hash r.hasher
  let existing ← s.read fun st => (st.revocations.live.get? key).bind (·.value)
  let outcome :=
    match existing with
    | none => PutOutcome.inserted
    | some old => if isLater r.revoked old.revocation.revoked then .replaced else .kept
  if outcome == .kept then return outcome
  let _ ← s.write (·.revocations) (fun st t => { st with revocations := t }) key (some rev)
  return outcome

def getRevocation (s : Store) (fingerprint hash hasher : String) :
    IO (Option Trust.SignedRevocation) :=
  s.read fun st =>
    (st.revocations.live.get? (revocationKey fingerprint hash hasher)).bind (·.value)

/--
§6.2 rule 2: is a certificate asserted at `asserted` suppressed?

A revocation suppresses exactly those certificates with the same triple whose
`asserted` is **not later** than `revoked`.  Rule 3 falls straight out of that:
re-issuing afterwards asserts later, so it reinstates by itself and needs no
second message.
-/
def isRevoked (s : Store) (fingerprint hash hasher asserted : String) : IO Bool := do
  match ← s.getRevocation fingerprint hash hasher with
  | none => return false
  | some rev => return !isLater asserted rev.revocation.revoked

/-- Everything stored for a hash, with §6.2 applied unless asked otherwise. -/
def certificatesByHash (s : Store) (hash : String) (hasher : Option String := none)
    (includeRevoked : Bool := false) : IO (Array StoredCertificate) :=
  s.state.atomically do
    let st ← get
    let mut out := #[]
    for row in st.certificates.liveRows do
      let some cert := row.value | continue
      let claim := cert.entry.claim
      if claim.hash.toLower != hash.toLower then continue
      if let some h := hasher then
        if claim.hasher != h then continue
      if !includeRevoked then
        let key := revocationKey cert.entry.fingerprint claim.hash claim.hasher
        if let some rev := (st.revocations.live.get? key).bind (·.value) then
          if !isLater claim.asserted rev.revocation.revoked then continue
      out := out.push cert
    return out

/-- Everything signed by one key, §6.2 applied. -/
def certificatesByFingerprint (s : Store) (fingerprint : String) :
    IO (Array StoredCertificate) := do
  let all ← s.read fun st => st.certificates.liveRows.filterMap (·.value)
  let wanted := fingerprint.toLower
  let mut out := #[]
  for cert in all do
    if cert.entry.fingerprint.toLower != wanted then continue
    let claim := cert.entry.claim
    if ← s.isRevoked cert.entry.fingerprint claim.hash claim.hasher claim.asserted then continue
    out := out.push cert
  return out

/-! ### Export (§4.1) -/

/--
Certificates in cursor order, for a peer catching up.

Tombstones are on the page too, as rows with no value: a peer that only ever saw
present rows would never learn that one went away.  §6.2 is *not* applied here —
revocations travel in the same bundle (§6, rule 4) and the receiver applies them
itself, which is what lets a withdrawal survive being relayed by a node that
never held the certificate it withdraws.
-/
def certificatesSince (s : Store) (since : String := "") (limit : Nat := 500) :
    IO (Page StoredCertificate) :=
  s.read fun st => st.certificates.page (Cursor.decode? since) limit

def revocationsSince (s : Store) (since : String := "") (limit : Nat := 500) :
    IO (Page Trust.SignedRevocation) :=
  s.read fun st => st.revocations.page (Cursor.decode? since) limit

/-! ### Peers (§5) -/

/-- Record a peer verbatim, overwriting whatever was there.  The operator's word. -/
def putPeer (s : Store) (peer : Peer) : IO Unit := do
  let addedMs ← if peer.addedMs != 0 then pure peer.addedMs else nowMs
  let _ ← s.write (·.peers) (fun st t => { st with peers := t })
    (tupleKey [peer.url]) (some { peer with addedMs })

def getPeer (s : Store) (url : String) : IO (Option Peer) :=
  s.read fun st => (st.peers.live.get? (tupleKey [url])).bind (·.value)

def listPeers (s : Store) (statuses : Array PeerStatus := #[]) : IO (Array Peer) := do
  let all ← s.read fun st => st.peers.liveRows.filterMap (·.value)
  let kept := if statuses.isEmpty then all else all.filter (statuses.contains ·.status)
  return kept.qsort fun a b => a.url < b.url

/-- §5.3: the peers this node queries itself, and only those. -/
def queriedPeers (s : Store) : IO (Array Peer) := s.listPeers #[.seed, .active]

/-- Move a peer between the states of §5.1.  Returns false if there is no such peer. -/
def setPeerStatus (s : Store) (url : String) (status : PeerStatus) : IO Bool := do
  match ← s.getPeer url with
  | none => return false
  | some peer =>
    s.putPeer { peer with status }
    return true

/--
What §5.2's announcement is allowed to do.

`blocked` is absorbing: discovery never re-admits a peer an operator has shut
out, which is the whole difference between `blocked` and `candidate`.  A `seed`
stays a seed, because it was configured rather than discovered.  Otherwise
`autodiscover` decides between `active` and `candidate`, and it defaults to off:
a protocol that adds peers without the operator's say-so is one where a stranger
can make a node issue requests on their behalf.
-/
def discoverPeer (s : Store) (url : String) (name : String) (autodiscover : Bool) :
    IO PeerStatus := do
  let proposed := if autodiscover then PeerStatus.active else .candidate
  match ← s.getPeer url with
  | some peer =>
    let status :=
      match peer.status with
      | .blocked => .blocked
      | .seed => .seed
      | .active => .active
      | .candidate => proposed
    s.putPeer { peer with name := if name.isEmpty then peer.name else name, status }
    return status
  | none =>
    s.putPeer { url, name, status := proposed }
    return proposed

/-- Note the outcome of a pull: how far it got, and what went wrong if anything. -/
def notePeerSeen (s : Store) (url cursor error : String) : IO Unit := do
  match ← s.getPeer url with
  | none => return ()
  | some peer =>
    s.putPeer { peer with cursor, lastError := error, lastSeenMs := ← nowMs }

def forgetPeer (s : Store) (url : String) : IO Unit := do
  let _ ← s.write (·.peers) (fun st t => { st with peers := t }) (tupleKey [url]) none

/-! ### Identities, sessions, follows -/

def putIdentity (s : Store) (identity : Identity) : IO Unit := do
  let createdMs ← if identity.createdMs != 0 then pure identity.createdMs else nowMs
  let _ ← s.write (·.identities) (fun st t => { st with identities := t })
    (tupleKey [identity.login]) (some { identity with createdMs })

def getIdentity (s : Store) (login : String) : IO (Option Identity) :=
  s.read fun st => (st.identities.live.get? (tupleKey [login])).bind (·.value)

def putSession (s : Store) (session : Session) : IO Unit := do
  let createdMs ← if session.createdMs != 0 then pure session.createdMs else nowMs
  let _ ← s.write (·.sessions) (fun st t => { st with sessions := t })
    (tupleKey [session.tokenSha256]) (some { session with createdMs })

/-- Resolve a bearer token by its digest.  The token itself is never stored. -/
def getSession (s : Store) (tokenSha256 : String) : IO (Option Session) :=
  s.read fun st => (st.sessions.live.get? (tupleKey [tokenSha256])).bind (·.value)

def deleteSession (s : Store) (tokenSha256 : String) : IO Unit := do
  let _ ← s.write (·.sessions) (fun st t => { st with sessions := t })
    (tupleKey [tokenSha256]) none

def putFollow (s : Store) (follow : Follow) : IO Unit := do
  let addedMs ← if follow.addedMs != 0 then pure follow.addedMs else nowMs
  let _ ← s.write (·.follows) (fun st t => { st with follows := t })
    (tupleKey [follow.truster, follow.kind, follow.target]) (some { follow with addedMs })

def deleteFollow (s : Store) (truster kind target : String) : IO Unit := do
  let _ ← s.write (·.follows) (fun st t => { st with follows := t })
    (tupleKey [truster, kind, target]) none

def listFollows (s : Store) (truster : String) : IO (Array Follow) := do
  let all ← s.read fun st => st.follows.liveRows.filterMap (·.value)
  return all.filter (·.truster == truster)

/-! ### Housekeeping -/

/-- §2's `counts`: live certificates, and the peers this node queries. -/
def counts (s : Store) : IO (Nat × Nat) := do
  let certificates ← s.read fun st => (st.certificates.liveRows.filterMap (·.value)).size
  let peers ← s.queriedPeers
  return (certificates, peers.size)

/-- Rewrite every log, keeping only what still determines the store's state. -/
def compact (s : Store) : IO Unit :=
  s.state.atomically do
    let st ← get
    let certificates ← st.certificates.compact st.opts
    let revocations ← st.revocations.compact st.opts
    let peers ← st.peers.compact st.opts
    let identities ← st.identities.compact st.opts
    let sessions ← st.sessions.compact st.opts
    let follows ← st.follows.compact st.opts
    set { st with certificates, revocations, peers, identities, sessions, follows }

/-- Records on disk and live rows for the certificate log; for tests and for compaction. -/
def certificateLogSize (s : Store) : IO (Nat × Nat) :=
  s.read fun st => (st.certificates.total, st.certificates.live.size)

/-- Flush every handle.  Closing is the process exiting; there is nothing else to do. -/
def flush (s : Store) : IO Unit :=
  s.state.atomically do
    let st ← get
    st.certificates.handle.flush
    st.revocations.handle.flush
    st.peers.handle.flush
    st.identities.handle.flush
    st.sessions.handle.flush
    st.follows.handle.flush

end Store

end TrustServer
