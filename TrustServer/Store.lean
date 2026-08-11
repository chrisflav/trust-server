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

/--
§3.1's two assurances, read off the row rather than stored beside it.

A row carries a signature exactly when this node checked one before writing it —
nothing here ever stores an unverified signature — so `signed` and `attested`
are decided by the entry itself and there is no second field that could come to
disagree with it.
-/
def StoredCertificate.assurance (c : StoredCertificate) : String :=
  if c.entry.signature.isEmpty then "attested" else "signed"

/--
Whether §3.1 lets this row leave the node.

`attested` is a statement about *this server's* authentication; there is nothing
in it for a receiver to check, so it stays where it was made.
-/
def StoredCertificate.federates (c : StoredCertificate) : Bool :=
  !c.entry.signature.isEmpty && !c.entry.key.isEmpty && !c.entry.fingerprint.isEmpty

/-- Issued here, rather than relayed to us. -/
def StoredCertificate.isLocal (c : StoredCertificate) : Bool := c.fromPeer.isEmpty

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
An armoured **public** key, and how firmly it is tied to an account.

`verifiedVia` is a claim about ownership and the three values are not
interchangeable: `github` means the account publishes this key itself, through a
party that is not us; `self` means somebody pasted it here while signed in;
`remote` means it arrived attached to a federated entry and is tied to nothing
this node checked.  Presenting the second as the first would be exactly the
unverified binding §1 forbids.
-/
structure PublicKey where
  fingerprint : String
  /-- The account that registered it.  Empty for a key seen only on the wire. -/
  login : String
  armored : String
  verifiedVia : String := "self"
  addedMs : Nat := 0
  deriving Inhabited, Repr, ToJson, FromJson

/-- What a stored secret is for.  All three are opaque values; only their lifetimes differ. -/
inductive SessionKind where
  /-- A browser session, held in a cookie. -/
  | browser
  /-- A command-line token, which never expires until it is revoked. -/
  | api
  /-- The anti-forgery `state` of an OAuth round trip; minutes, not days. -/
  | oauthState
  deriving Inhabited, Repr, DecidableEq, BEq

namespace SessionKind

def toString : SessionKind → String
  | .browser => "session" | .api => "token" | .oauthState => "state"

def ofString? : String → Option SessionKind
  | "session" => some .browser | "token" => some .api | "state" => some .oauthState
  | _ => none

end SessionKind

instance : ToJson SessionKind where toJson k := Json.str k.toString
instance : FromJson SessionKind where
  fromJson? j := do
    let s ← j.getStr?
    match SessionKind.ofString? s with
    | some kind => return kind
    | none => throw s!"`{s}` is not a kind of session"

/--
A credential: a random value, who it speaks for, and when it dies.

**The token is stored as it stands, and that is a deliberate, documented
trade.**  The TypeScript keeps only a SHA-256 digest, so that a leaked database
does not hand anyone the ability to publish as someone else.  Lean v4.32.0 has
no SHA-2 anywhere in its toolchain and this package refuses to grow a hand-rolled
one — a hash function written to make a comment true is worse than the comment
being false.  So the store file is exactly as sensitive as the sessions in it,
which is a thing an operator can be told, rather than a thing they might
believe wrongly.

What the digest bought is not, in fact, what makes a certificate worth
anything: a token says who is publishing, and cannot forge a signature.

`id` is not the secret.  It exists so a token can be listed and revoked without
the value ever coming back out of the server.
-/
structure Session where
  /-- The opaque value the client presents. -/
  token : String
  /-- A name for the row that is safe to hand out. -/
  id : String := ""
  kind : SessionKind := .browser
  /-- The identity it speaks for.  Empty for an OAuth state, which speaks for nobody yet. -/
  login : String := ""
  /-- What its owner called it, for a list of tokens that means something. -/
  name : String := ""
  createdMs : Nat := 0
  /-- Epoch milliseconds after which it is dead.  `0` never expires. -/
  expiresMs : Nat := 0
  lastUsedMs : Nat := 0
  deriving Inhabited, Repr, ToJson, FromJson

/-- Whether a credential is still alive at `now`, in epoch milliseconds. -/
def Session.alive (s : Session) (now : Nat) : Bool := s.expiresMs == 0 || now < s.expiresMs

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

/--
The key an `attested` row is filed under.

§3.5's triple identifies a *signed* entry, and an unsigned one has no
fingerprint to put in it.  Filing every attested row under the empty
fingerprint would make two accounts' assertions about the same hash collide, so
the issuer stands in for the key that is missing.  The prefix keeps that
namespace disjoint from any real fingerprint, which is hex.
-/
def attestedKey (issuer hash hasher : String) : String :=
  certificateKey s!"attested:{issuer}" hash hasher

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
  keys : Table PublicKey
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
  let keys ← Table.load (α := PublicKey) (dir / "keys.jsonl")
  let sessions ← Table.load (α := Session) (dir / "sessions.jsonl")
  let follows ← Table.load (α := Follow) (dir / "follows.jsonl")
  -- The next row id continues past everything already written; reusing one
  -- would make two rows share a cursor position, which is the one thing the
  -- row id exists to prevent.
  let nextSeq := 1 + max (maxSeq certificates.liveRows)
    (max (maxSeq revocations.liveRows) (max (maxSeq peers.liveRows)
      (max (maxSeq identities.liveRows) (max (maxSeq keys.liveRows)
        (max (maxSeq sessions.liveRows) (maxSeq follows.liveRows))))))
  let certificates ← certificates.compactIfNeeded opts
  let revocations ← revocations.compactIfNeeded opts
  let peers ← peers.compactIfNeeded opts
  let identities ← identities.compactIfNeeded opts
  let keys ← keys.compactIfNeeded opts
  let sessions ← sessions.compactIfNeeded opts
  let follows ← follows.compactIfNeeded opts
  let state ← Std.Mutex.new
    { dir, opts, nextSeq, certificates, revocations, peers, identities, keys, sessions, follows }
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
  let key :=
    if cert.entry.fingerprint.isEmpty then attestedKey cert.hints.issuer claim.hash claim.hasher
    else certificateKey cert.entry.fingerprint claim.hash claim.hasher
  let existing ← s.read fun st => (st.certificates.live.get? key).bind (·.value)
  let outcome :=
    match existing with
    | none => PutOutcome.inserted
    | some old => if Trust.laterThan claim.asserted old.entry.claim.asserted then .replaced else .kept
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
    | some old => if Trust.laterThan r.revoked old.revocation.revoked then .replaced else .kept
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
  | some rev => return Trust.notLaterThan asserted rev.revocation.revoked

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
          if Trust.notLaterThan claim.asserted rev.revocation.revoked then continue
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

/-- Every live certificate row, §6.2 not applied.  The caller decides what to hide. -/
def liveCertificates (s : Store) : IO (Array StoredCertificate) :=
  s.read fun st => st.certificates.liveRows.filterMap (·.value)

/--
Withdraw an account's own rows for a hash from this node's log.

Only what this node originated and only what that account issued: a copy that
arrived from a peer is not ours to take back, and a signed withdrawal (§6) is
the form that travels.  Returns how many rows were tombstoned.
-/
def withdrawLocal (s : Store) (issuer hash : String) : IO Nat := do
  let all ← s.read fun st => st.certificates.live.toArray
  let mut removed := 0
  for (key, row) in all do
    let some cert := row.value | continue
    if !cert.isLocal then continue
    if cert.hints.issuer != issuer then continue
    if cert.entry.claim.hash.toLower != hash.toLower then continue
    let _ ← s.write (·.certificates) (fun st t => { st with certificates := t }) key none
    removed := removed + 1
  return removed

/-- Withdrawals matching a filter, for the bundle a query answers with. -/
def revocationsFor (s : Store) (hash : Option String := none) (hasher : Option String := none)
    (fingerprint : Option String := none) : IO (Array Trust.SignedRevocation) := do
  let all ← s.read fun st => st.revocations.liveRows.filterMap (·.value)
  return all.filter fun rev =>
    let r := rev.revocation
    (match hash with | some h => r.hash.toLower == h.toLower | none => true) &&
      (match hasher with | some h => r.hasher == h | none => true) &&
      (match fingerprint with | some f => r.fingerprint.toLower == f.toLower | none => true)

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

/-! ### Identities, keys, sessions, follows -/

def putIdentity (s : Store) (identity : Identity) : IO Unit := do
  let createdMs ← if identity.createdMs != 0 then pure identity.createdMs else nowMs
  let _ ← s.write (·.identities) (fun st t => { st with identities := t })
    (tupleKey [identity.login]) (some { identity with createdMs })

def getIdentity (s : Store) (login : String) : IO (Option Identity) :=
  s.read fun st => (st.identities.live.get? (tupleKey [login])).bind (·.value)

/-- The account a GitHub id belongs to, whatever it currently calls itself. -/
def identityByGitHubId (s : Store) (githubId : Int) : IO (Option Identity) := do
  if githubId < 0 then return none
  let all ← s.read fun st => st.identities.liveRows.filterMap (·.value)
  return all.find? (·.githubId == githubId)

def listIdentities (s : Store) : IO (Array Identity) :=
  s.read fun st => st.identities.liveRows.filterMap (·.value)

/--
Follow a GitHub rename.

Identities, keys and follows are all filed under the login, because that is what
a certificate's hints and a trust list name.  A renamed account is still the
same account — its GitHub id has not moved — so the rows move with it rather
than the person losing their keys and their trust list to a change of name.
-/
def renameIdentity (s : Store) (oldLogin newLogin : String) : IO Unit := do
  if oldLogin == newLogin then return ()
  let some identity ← s.getIdentity oldLogin | return ()
  let _ ← s.write (·.identities) (fun st t => { st with identities := t })
    (tupleKey [oldLogin]) none
  s.putIdentity { identity with login := newLogin }
  let keys ← s.read fun st => st.keys.live.toArray
  for (key, row) in keys do
    let some stored := row.value | continue
    if stored.login != oldLogin then continue
    let _ ← s.write (·.keys) (fun st t => { st with keys := t }) key none
    let _ ← s.write (·.keys) (fun st t => { st with keys := t })
      (tupleKey [newLogin, stored.fingerprint.toLower]) (some { stored with login := newLogin })
  let follows ← s.read fun st => st.follows.live.toArray
  for (key, row) in follows do
    let some follow := row.value | continue
    if follow.truster != oldLogin then continue
    let _ ← s.write (·.follows) (fun st t => { st with follows := t }) key none
    let _ ← s.write (·.follows) (fun st t => { st with follows := t })
      (tupleKey [newLogin, follow.kind, follow.target]) (some { follow with truster := newLogin })

/-- Register a public key against an account.  Nothing else is ever stored beside one. -/
def putKey (s : Store) (key : PublicKey) : IO Unit := do
  let addedMs ← if key.addedMs != 0 then pure key.addedMs else nowMs
  let _ ← s.write (·.keys) (fun st t => { st with keys := t })
    (tupleKey [key.login, key.fingerprint.toLower])
    (some { key with fingerprint := key.fingerprint.toLower, addedMs })

def keysForLogin (s : Store) (login : String) : IO (Array PublicKey) := do
  let all ← s.read fun st => st.keys.liveRows.filterMap (·.value)
  return all.filter (·.login == login)

/--
Any key this node has seen, wherever it saw it.

Falls back to the key a federated entry travelled with, marked `remote`: a
reader checking a relayed entry has a fingerprint and nothing else they could
have looked up, and that key is tied to nothing this node verified about an
account.
-/
def keyByFingerprint (s : Store) (fingerprint : String) : IO (Option PublicKey) := do
  let wanted := fingerprint.toLower
  let registered ← s.read fun st => st.keys.liveRows.filterMap (·.value)
  match registered.find? (·.fingerprint.toLower == wanted) with
  | some key => return some key
  | none =>
    let certificates ← s.liveCertificates
    match certificates.find? (fun c => c.entry.fingerprint.toLower == wanted &&
        !c.entry.key.isEmpty) with
    | some cert => return some {
        fingerprint := wanted, login := cert.hints.issuer, armored := cert.entry.key,
        verifiedVia := "remote" }
    | none => return none

/--
Write down a credential.

Filed under the value itself, so that presenting it is a lookup rather than a
scan.  The comparison that *decides* anything is still `secureEqual` in
`TrustServer.Auth`: a hash-map probe is a hint, not an authorisation.
-/
def putSession (s : Store) (session : Session) : IO Unit := do
  let createdMs ← if session.createdMs != 0 then pure session.createdMs else nowMs
  let _ ← s.write (·.sessions) (fun st t => { st with sessions := t })
    (tupleKey [session.token]) (some { session with createdMs })

/-- The row a presented value names, if there is one.  Expiry is the caller's to check. -/
def getSession (s : Store) (token : String) : IO (Option Session) :=
  s.read fun st => (st.sessions.live.get? (tupleKey [token])).bind (·.value)

/-- A credential by its public id, which is what a listing hands out. -/
def sessionById (s : Store) (id : String) : IO (Option Session) := do
  if id.isEmpty then return none
  let all ← s.read fun st => st.sessions.liveRows.filterMap (·.value)
  return all.find? (·.id == id)

def listSessions (s : Store) (login : String) (kind : SessionKind) : IO (Array Session) := do
  let all ← s.read fun st => st.sessions.liveRows.filterMap (·.value)
  return all.filter fun session => session.login == login && session.kind == kind

def deleteSession (s : Store) (token : String) : IO Unit := do
  let _ ← s.write (·.sessions) (fun st t => { st with sessions := t })
    (tupleKey [token]) none

/-- Drop everything that has died, so an OAuth round trip cannot grow the log forever. -/
def expireSessions (s : Store) : IO Nat := do
  let now ← nowMs
  let all ← s.read fun st => st.sessions.live.toArray
  let mut dropped := 0
  for (key, row) in all do
    let some session := row.value | continue
    if session.alive now then continue
    let _ ← s.write (·.sessions) (fun st t => { st with sessions := t }) key none
    dropped := dropped + 1
  return dropped

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
    let keys ← st.keys.compact st.opts
    let sessions ← st.sessions.compact st.opts
    let follows ← st.follows.compact st.opts
    set { st with certificates, revocations, peers, identities, keys, sessions, follows }

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
    st.keys.handle.flush
    st.sessions.handle.flush
    st.follows.handle.flush

end Store

end TrustServer
