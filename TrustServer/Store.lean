import Lean
import Std.Sync.Mutex
import Std.Time
import SQLite
import Trust.Cert

/-!
# The store: SQLite

## Why SQLite, and why it costs no toolchain bump

This used to be a directory of append-only JSONL files, on the belief that
`leansqlite` pins `leanprover/lean4:v4.34.0-rc1` and that following it would drag
this package's toolchain — and with it the pinned `semantic_hash` revision that
every certificate hash is computed with — along behind the storage engine.

That belief was wrong.  `leansqlite` publishes **a tag per Lean release**, and
`v4.32.0` is exactly the toolchain in `lean-toolchain`.  Nothing about moving to
a database touches what a stored hash means.  The one real cost is a C compiler
at build time, because the SQLite amalgamation is compiled and statically linked
into the binary; a node that only *runs* needs nothing new, which is why the
runtime stage of `docker/Dockerfile` is unchanged.

## What the database gives that the log did not

* **Real deletes.**  A tombstone was an artefact of a file you may only append
  to.  Nothing outside this module ever read one: both export paths
  (`Routes.exportBundle` and `Federation.Service.exportBundle`) drop rows with no
  value before serialising, because §4 has no shape for "this row went away".  A
  deletion therefore travelled no further than this node under the log either,
  so removing tombstones changes nothing a peer can observe.
* **Durability that is the engine's problem.**  v4.32.0 exposes no `fsync` on
  `IO.FS.Handle`, so the log shelled out to `sync --data` once per write.  That
  subprocess is gone: `Options.fsync` now selects `PRAGMA synchronous`, `FULL`
  against power loss and `NORMAL` against this process dying, which is precisely
  what the flag always claimed to mean.
* **Concurrency.**  WAL mode plus a busy timeout, so a reader never blocks a
  writer and a second connection to the same file — a `Store.open` of a directory
  that is already open — works rather than deadlocks.

## What has not changed, and must not

* **§4.3's cursor.**  A cursor is still `<epoch-ms>.<row-id>`, still the pair
  `(updated_at, seq)`, and `seq` is still allocated from **one counter shared by
  every table** so the order it induces is total: two rows written in the same
  millisecond, or one certificate and one revocation, still have a definite
  order.  `Routes.exportBundle` compares a certificate's cursor against a
  revocation's, which is only meaningful because of that.  The counter lives in
  the database (`seq_counter`) rather than in memory, and is bumped inside the
  same transaction as the row it numbers.
* **§3.5 and §6.2.**  Both are still decided here, and both still go through
  core's `Trust.laterThan` and `Trust.notLaterThan`.  No timestamp is ever
  compared in SQL: the ordering rule belongs to the protocol library and has
  forked once already.

## The rule about SQL

Every value that reaches SQLite is a bound parameter, via the `sql!` macro or
via `bindAll`.  SQL text in this file is built only from string literals written
in this file — never from a fingerprint, a hash, a login or a token.  This node
takes input from strangers.
-/

namespace TrustServer

open Lean (Json ToJson FromJson toJson fromJson?)
open System (FilePath)
-- Selective, because `SQLite.Row` would collide with this module's `Row`.  The
-- `sql!` macro needs `NullableQueryParam` resolvable at the use site.
open SQLite (NullableQueryParam)

/-! ## Time -/

/-- The current time in epoch milliseconds, which is what a cursor is made of. -/
def nowMs : IO Nat := do
  let ts ← Std.Time.Timestamp.now
  return ts.toMillisecondsSinceUnixEpoch.val.toNat


/-! ## Cursors (§4.3) -/

/--
A position in the store: the millisecond a row last changed, and the row id.

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

/--
The bottom of the order, which "no cursor given" means.

Every allocated `seq` is at least 1, so no stored row can sit at or below
`(0, 0)` and a page from here is a page from the beginning.  Having a real
bottom element lets one `WHERE` clause serve both the first request and a
resume, which is what keeps the index on `(updated_at, seq)` doing the work.
-/
def bottom : Cursor := { ms := 0, seq := 0 }

end Cursor

/-! ## Records -/

/--
One row of one table, with its position in the cursor order.

`value` is an `Option` because callers were written against a log in which a
delete appended a valueless row.  A delete is now a delete, so a row that comes
back from the database always carries a value; the shape is kept because
`Routes.exportBundle` and the tests are written in terms of it.
-/
structure Row (α : Type) where
  seq : Nat
  updatedAt : Nat
  /-- The record's identity within its table. -/
  key : String
  value : Option α
  deriving Inhabited

def Row.cursor (r : Row α) : Cursor := { ms := r.updatedAt, seq := r.seq }

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

/-- The rows that still exist. -/
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
being false.  So the database file is exactly as sensitive as the sessions in it,
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

/-! ## Options -/

/-- How durable a write has to be before it is allowed to return. -/
structure Options where
  /--
  Whether a committed write has reached the platter before it returns.

  On, `PRAGMA synchronous=FULL`: SQLite fsyncs the write-ahead log at every
  commit, so a write that returned survives the machine losing power.  Off,
  `PRAGMA synchronous=NORMAL`: it survives this process dying but not the
  machine.  The old store spelled the same distinction as a `sync --data`
  subprocess per append, because v4.32.0 has no `fsync` on `IO.FS.Handle`.  It
  is now a pragma, and the subprocess is gone.
  -/
  fsync : Bool := true
  deriving Inhabited

/-! ## The database -/

/--
How long a statement retries a locked database before failing.

WAL means readers and writers do not block each other, so this is only reached
when two *writers* meet — two processes on one store directory.  Five seconds is
long enough to ride out a federation pull's transaction and short enough that a
wedged node is reported rather than hanging.
-/
private def busyTimeoutMs : Int32 := 5000

/--
What this build knows how to read.

Bumping it is the signal that a migration is needed; a database written by a
newer build is refused rather than silently misread.
-/
private def schemaVersion : Nat := 1

/--
The whole schema, created idempotently on every open.

Every table carries `key` (its identity, the same length-prefixed tuple the log
filed rows under), `seq` and `updated_at` — the two halves of a §4.3 cursor —
and is indexed on `(updated_at, seq)` so a page is an index range scan rather
than a sort.

`*_lower` columns exist because the protocol compares hashes and fingerprints
case-insensitively and that folding is *Lean's* `String.toLower`, computed
before the value is bound.  Relying on SQL's `lower()` or `COLLATE NOCASE`
would be a second implementation of a comparison the rest of the system already
makes.
-/
private def schema : String := "
CREATE TABLE IF NOT EXISTS schema_version (
  id      INTEGER PRIMARY KEY CHECK (id = 0),
  version INTEGER NOT NULL
);

-- One counter for the whole store, so that a certificate's cursor and a
-- revocation's cursor are comparable: `Routes.exportBundle` takes the lesser of
-- the two ends, which is meaningless if the ids come from separate sequences.
CREATE TABLE IF NOT EXISTS seq_counter (
  id   INTEGER PRIMARY KEY CHECK (id = 0),
  next INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS certificates (
  key                   TEXT    PRIMARY KEY,
  seq                   INTEGER NOT NULL UNIQUE,
  updated_at            INTEGER NOT NULL,
  decl                  TEXT    NOT NULL,
  hash                  TEXT    NOT NULL,
  hash_lower            TEXT    NOT NULL,
  hasher                TEXT    NOT NULL,
  repo                  TEXT    NOT NULL,
  commit_ref            TEXT    NOT NULL,
  toolchain             TEXT    NOT NULL,
  asserted              TEXT    NOT NULL,
  note                  TEXT    NOT NULL,
  signature             TEXT    NOT NULL,
  key_armored           TEXT    NOT NULL,
  fingerprint           TEXT    NOT NULL,
  fingerprint_lower     TEXT    NOT NULL,
  hint_issuer           TEXT    NOT NULL,
  hint_key_verified_via TEXT    NOT NULL,
  hint_origin           TEXT    NOT NULL,
  from_peer             TEXT    NOT NULL,
  fetched_ms            INTEGER NOT NULL
) STRICT;
CREATE INDEX IF NOT EXISTS certificates_cursor
  ON certificates (updated_at, seq);
CREATE INDEX IF NOT EXISTS certificates_hash
  ON certificates (hash_lower, hasher);
CREATE INDEX IF NOT EXISTS certificates_fingerprint
  ON certificates (fingerprint_lower);

CREATE TABLE IF NOT EXISTS revocations (
  key                TEXT    PRIMARY KEY,
  seq                INTEGER NOT NULL UNIQUE,
  updated_at         INTEGER NOT NULL,
  fingerprint        TEXT    NOT NULL,
  fingerprint_lower  TEXT    NOT NULL,
  hash               TEXT    NOT NULL,
  hash_lower         TEXT    NOT NULL,
  hasher             TEXT    NOT NULL,
  reason             TEXT    NOT NULL,
  revoked            TEXT    NOT NULL,
  signature          TEXT    NOT NULL,
  key_armored        TEXT    NOT NULL,
  signer_fingerprint TEXT    NOT NULL
) STRICT;
CREATE INDEX IF NOT EXISTS revocations_cursor
  ON revocations (updated_at, seq);
CREATE INDEX IF NOT EXISTS revocations_hash
  ON revocations (hash_lower, hasher);

CREATE TABLE IF NOT EXISTS peers (
  key          TEXT    PRIMARY KEY,
  seq          INTEGER NOT NULL UNIQUE,
  updated_at   INTEGER NOT NULL,
  url          TEXT    NOT NULL,
  name         TEXT    NOT NULL,
  status       TEXT    NOT NULL,
  cursor       TEXT    NOT NULL,
  last_seen_ms INTEGER NOT NULL,
  last_error   TEXT    NOT NULL,
  added_ms     INTEGER NOT NULL
) STRICT;
CREATE INDEX IF NOT EXISTS peers_cursor ON peers (updated_at, seq);

CREATE TABLE IF NOT EXISTS identities (
  key        TEXT    PRIMARY KEY,
  seq        INTEGER NOT NULL UNIQUE,
  updated_at INTEGER NOT NULL,
  login      TEXT    NOT NULL,
  github_id  INTEGER NOT NULL,
  avatar_url TEXT    NOT NULL,
  created_ms INTEGER NOT NULL
) STRICT;
CREATE INDEX IF NOT EXISTS identities_cursor ON identities (updated_at, seq);
CREATE INDEX IF NOT EXISTS identities_github ON identities (github_id);

CREATE TABLE IF NOT EXISTS keys (
  key          TEXT    PRIMARY KEY,
  seq          INTEGER NOT NULL UNIQUE,
  updated_at   INTEGER NOT NULL,
  fingerprint  TEXT    NOT NULL,
  login        TEXT    NOT NULL,
  armored      TEXT    NOT NULL,
  verified_via TEXT    NOT NULL,
  added_ms     INTEGER NOT NULL
) STRICT;
CREATE INDEX IF NOT EXISTS keys_cursor ON keys (updated_at, seq);
CREATE INDEX IF NOT EXISTS keys_login ON keys (login);
CREATE INDEX IF NOT EXISTS keys_fingerprint ON keys (fingerprint);

CREATE TABLE IF NOT EXISTS sessions (
  key          TEXT    PRIMARY KEY,
  seq          INTEGER NOT NULL UNIQUE,
  updated_at   INTEGER NOT NULL,
  token        TEXT    NOT NULL,
  id           TEXT    NOT NULL,
  kind         TEXT    NOT NULL,
  login        TEXT    NOT NULL,
  name         TEXT    NOT NULL,
  created_ms   INTEGER NOT NULL,
  expires_ms   INTEGER NOT NULL,
  last_used_ms INTEGER NOT NULL
) STRICT;
CREATE INDEX IF NOT EXISTS sessions_cursor ON sessions (updated_at, seq);
CREATE INDEX IF NOT EXISTS sessions_owner ON sessions (login, kind);
CREATE INDEX IF NOT EXISTS sessions_id ON sessions (id);

CREATE TABLE IF NOT EXISTS follows (
  key        TEXT    PRIMARY KEY,
  seq        INTEGER NOT NULL UNIQUE,
  updated_at INTEGER NOT NULL,
  truster    TEXT    NOT NULL,
  target     TEXT    NOT NULL,
  kind       TEXT    NOT NULL,
  label      TEXT    NOT NULL,
  added_ms   INTEGER NOT NULL
) STRICT;
CREATE INDEX IF NOT EXISTS follows_cursor ON follows (updated_at, seq);
CREATE INDEX IF NOT EXISTS follows_truster ON follows (truster);

INSERT OR IGNORE INTO schema_version (id, version) VALUES (0, 1);
INSERT OR IGNORE INTO seq_counter (id, next) VALUES (0, 1);
"

/-! ### Binding

A value never becomes SQL text.  It is either interpolated by `sql!`, which
turns it into a `?n` parameter, or it goes through `bindAll`.
-/

/-- A value on its way into a bound parameter. -/
private inductive Val where
  | text (v : String)
  | count (v : Nat)
  | int (v : Int)
  | null
  deriving Inhabited

/-- Bind an array of values to `?1`, `?2`, … in order. -/
private def bindAll (stmt : SQLite.Stmt) (vals : Array Val) : IO Unit := do
  for i in [0:vals.size] do
    let index := Nat.toInt32 (i + 1)
    match vals[i]! with
    | .text v => stmt.bindText index v
    | .count v => stmt.bindInt64 index (Int64.ofNat v)
    | .int v => stmt.bindInt64 index (Int64.ofInt v)
    | .null => stmt.bindNull index

/-- `?1, ?2, …, ?n`, for an insert whose column list is a literal above. -/
private def placeholders (n : Nat) : String :=
  String.intercalate ", " ((List.range n).map fun i => s!"?{i + 1}")

/-! ### Reading -/

private def txt (stmt : SQLite.Stmt) (i : Nat) : IO String :=
  stmt.columnText (Nat.toInt32 i)

private def num (stmt : SQLite.Stmt) (i : Nat) : IO Nat := do
  return (← stmt.columnInt64 (Nat.toInt32 i)).toInt.toNat

private def whole (stmt : SQLite.Stmt) (i : Nat) : IO Int := do
  return (← stmt.columnInt64 (Nat.toInt32 i)).toInt

/-- Every row a statement will yield, read left to right by `rd`. -/
private partial def collect (stmt : SQLite.Stmt) (rd : SQLite.Stmt → IO α) : IO (Array α) :=
  go #[]
where
  go (acc : Array α) : IO (Array α) := do
    if ← stmt.step then go (acc.push (← rd stmt)) else return acc

/-- The first row, if there is one. -/
private def first? (stmt : SQLite.Stmt) (rd : SQLite.Stmt → IO α) : IO (Option α) := do
  if ← stmt.step then some <$> rd stmt else return none

/-! ### The tables, as columns and as Lean values

Each table has exactly one column list and one reader, so a schema change is one
edit rather than seven, and a `SELECT` whose columns had drifted out of step
with its reader cannot happen.
-/

private def certificateColumns : String :=
  "key, seq, updated_at, decl, hash, hasher, repo, commit_ref, toolchain, asserted, note, " ++
  "signature, key_armored, fingerprint, hint_issuer, hint_key_verified_via, hint_origin, " ++
  "from_peer, fetched_ms"

private def readCertificate (stmt : SQLite.Stmt) : IO (Row StoredCertificate) := do
  let claim : Trust.Claim := {
    decl := ← txt stmt 3, hash := ← txt stmt 4, hasher := ← txt stmt 5,
    repo := ← txt stmt 6, commit := ← txt stmt 7, toolchain := ← txt stmt 8,
    asserted := ← txt stmt 9, note := ← txt stmt 10 }
  let entry : Trust.Entry := {
    claim, signature := ← txt stmt 11, key := ← txt stmt 12, fingerprint := ← txt stmt 13 }
  let hints : Hints := {
    issuer := ← txt stmt 14, keyVerifiedVia := ← txt stmt 15, origin := ← txt stmt 16 }
  return {
    key := ← txt stmt 0, seq := ← num stmt 1, updatedAt := ← num stmt 2
    value := some { entry, hints, fromPeer := ← txt stmt 17, fetchedMs := ← num stmt 18 } }

private def revocationColumns : String :=
  "key, seq, updated_at, fingerprint, hash, hasher, reason, revoked, signature, " ++
  "key_armored, signer_fingerprint"

private def readRevocation (stmt : SQLite.Stmt) : IO (Row Trust.SignedRevocation) := do
  let revocation : Trust.Revocation := {
    fingerprint := ← txt stmt 3, hash := ← txt stmt 4, hasher := ← txt stmt 5,
    reason := ← txt stmt 6, revoked := ← txt stmt 7 }
  return {
    key := ← txt stmt 0, seq := ← num stmt 1, updatedAt := ← num stmt 2
    value := some {
      revocation, signature := ← txt stmt 8, key := ← txt stmt 9,
      fingerprint := ← txt stmt 10 } }

private def peerColumns : String :=
  "key, seq, updated_at, url, name, status, cursor, last_seen_ms, last_error, added_ms"

private def readPeer (stmt : SQLite.Stmt) : IO (Row Peer) := do
  let raw ← txt stmt 5
  let some status := PeerStatus.ofString? raw
    | throw <| IO.userError s!"`{raw}` is not a peer status"
  return {
    key := ← txt stmt 0, seq := ← num stmt 1, updatedAt := ← num stmt 2
    value := some {
      url := ← txt stmt 3, name := ← txt stmt 4, status, cursor := ← txt stmt 6,
      lastSeenMs := ← num stmt 7, lastError := ← txt stmt 8, addedMs := ← num stmt 9 } }

private def identityColumns : String :=
  "key, seq, updated_at, login, github_id, avatar_url, created_ms"

private def readIdentity (stmt : SQLite.Stmt) : IO (Row Identity) := do
  return {
    key := ← txt stmt 0, seq := ← num stmt 1, updatedAt := ← num stmt 2
    value := some {
      login := ← txt stmt 3, githubId := ← whole stmt 4, avatarUrl := ← txt stmt 5,
      createdMs := ← num stmt 6 } }

private def keyColumns : String :=
  "key, seq, updated_at, fingerprint, login, armored, verified_via, added_ms"

private def readKey (stmt : SQLite.Stmt) : IO (Row PublicKey) := do
  return {
    key := ← txt stmt 0, seq := ← num stmt 1, updatedAt := ← num stmt 2
    value := some {
      fingerprint := ← txt stmt 3, login := ← txt stmt 4, armored := ← txt stmt 5,
      verifiedVia := ← txt stmt 6, addedMs := ← num stmt 7 } }

private def sessionColumns : String :=
  "key, seq, updated_at, token, id, kind, login, name, created_ms, expires_ms, last_used_ms"

private def readSession (stmt : SQLite.Stmt) : IO (Row Session) := do
  let raw ← txt stmt 5
  let some kind := SessionKind.ofString? raw
    | throw <| IO.userError s!"`{raw}` is not a kind of session"
  return {
    key := ← txt stmt 0, seq := ← num stmt 1, updatedAt := ← num stmt 2
    value := some {
      token := ← txt stmt 3, id := ← txt stmt 4, kind, login := ← txt stmt 6,
      name := ← txt stmt 7, createdMs := ← num stmt 8, expiresMs := ← num stmt 9,
      lastUsedMs := ← num stmt 10 } }

private def followColumns : String :=
  "key, seq, updated_at, truster, target, kind, label, added_ms"

private def readFollow (stmt : SQLite.Stmt) : IO (Row Follow) := do
  return {
    key := ← txt stmt 0, seq := ← num stmt 1, updatedAt := ← num stmt 2
    value := some {
      truster := ← txt stmt 3, target := ← txt stmt 4, kind := ← txt stmt 5,
      label := ← txt stmt 6, addedMs := ← num stmt 7 } }

/-! ### Queries

`clause` is always a literal written in this file; everything a caller supplies
arrives in `binds`.
-/

private def selectRows (db : SQLite) (columns table clause : String) (binds : Array Val)
    (rd : SQLite.Stmt → IO α) : IO (Array α) := do
  let stmt ← db.prepare s!"SELECT {columns} FROM {table} {clause}"
  bindAll stmt binds
  collect stmt rd

private def selectRow? (db : SQLite) (columns table clause : String) (binds : Array Val)
    (rd : SQLite.Stmt → IO α) : IO (Option α) := do
  let stmt ← db.prepare s!"SELECT {columns} FROM {table} {clause}"
  bindAll stmt binds
  first? stmt rd

private def execWith (db : SQLite) (sql : String) (binds : Array Val) : IO Unit := do
  let stmt ← db.prepare sql
  bindAll stmt binds
  stmt.exec

/-- How many rows the statement just run touched. -/
private def changed (db : SQLite) : IO Nat := do
  return (← db.changes).toInt.toNat

/-! ### The cursor's page

One clause serves both a first request and a resume, because `Cursor.bottom` is
a real bottom of the order.  `LIMIT limit + 1` is how truncation is detected
without a second `COUNT`.
-/

private def pageOf (db : SQLite) (columns table : String) (since : Option Cursor) (limit : Nat)
    (rd : SQLite.Stmt → IO (Row α)) : IO (Page α) := do
  let from_ := since.getD Cursor.bottom
  let fetched ← selectRows db columns table
    ("WHERE updated_at > ?1 OR (updated_at = ?1 AND seq > ?2) " ++
      "ORDER BY updated_at ASC, seq ASC LIMIT ?3")
    #[.count from_.ms, .count from_.seq, .count (limit + 1)] rd
  let truncated := fetched.size > limit
  let rows := fetched.extract 0 limit
  let cursor :=
    match rows.back?, since with
    | some last, _ => last.cursor.encode
    -- Nothing new: hand back what was asked for, so an idle peer does not walk
    -- back to the beginning of the store.
    | none, some c => c.encode
    | none, none => ""
  return { rows, cursor, truncated }

/-! ## The store -/

/-- The open database, and the options it was opened with. -/
structure StoreState where
  dir : FilePath
  opts : Options
  db : SQLite

/--
One SQLite database, behind one lock.

The lock is not what makes the *data* consistent — transactions and WAL do that,
across processes as well as threads.  It is here because a `SQLite.Stmt` is not
safe to step from two threads at once, and because a read-decide-write such as
§3.5's collision rule has to see the same database it is about to change.
-/
structure Store where
  private state : Std.Mutex StoreState

namespace Store

/-- Do something with the connection, alone. -/
private def withDb (s : Store) (f : SQLite → IO β) : IO β :=
  s.state.atomically do
    let st ← get
    f st.db

/--
Do something with the connection, alone and in a transaction.

Every write goes through here.  Even a write of one row is two: the row, and the
counter its `seq` came from.
-/
private def write (s : Store) (f : SQLite → IO β) : IO β :=
  s.withDb fun db => db.transaction (mode := .immediate) (f db)

/--
Take the next row id and the current time.

Both under the caller's transaction, so the cursor order can never disagree with
the order the database is in, and two processes writing the same store cannot be
handed the same id.
-/
private def alloc (db : SQLite) : IO (Nat × Nat) := do
  let bump ← db.prepare "UPDATE seq_counter SET next = next + 1 WHERE id = 0"
  bump.exec
  let sel ← db.prepare "SELECT next - 1 FROM seq_counter WHERE id = 0"
  let some seq ← first? sel (num · 0)
    | throw <| IO.userError "the store's sequence counter is missing"
  return (seq, ← nowMs)

/-- Open (creating if need be) the store in `dir`. -/
def «open» (dir : FilePath) (opts : Options := {}) : IO Store := do
  IO.FS.createDirAll dir
  let db ← SQLite.open (dir / "store.db") (busyTimeoutMs := busyTimeoutMs)
  -- WAL first: a reader never blocks a writer, and a second connection to the
  -- same file — which `Store.open` of an already-open directory is — works.
  db.exec "PRAGMA journal_mode=WAL"
  let mode ← db.prepare "PRAGMA journal_mode"
  let some journal ← first? mode (txt · 0)
    | throw <| IO.userError s!"{dir}: SQLite would not report its journal mode"
  if journal.toLower != "wal" then
    throw <| IO.userError
      s!"{dir}: could not put the store in WAL mode (it is `{journal}`); \
         a filesystem that does not support it cannot hold this store"
  db.exec (if opts.fsync then "PRAGMA synchronous=FULL" else "PRAGMA synchronous=NORMAL")
  -- No table declares a foreign key today.  It is on so that one added by a
  -- migration is enforced from the moment it exists, rather than from whenever
  -- somebody remembers this pragma is off by default.
  db.exec "PRAGMA foreign_keys=ON"
  db.exec schema
  let found ← selectRow? db "version" "schema_version" "WHERE id = 0" #[] (num · 0)
  let some version := found
    | throw <| IO.userError s!"{dir}: the store has no schema version"
  if version > schemaVersion then
    throw <| IO.userError
      s!"{dir}: the store is at schema version {version}, and this build knows {schemaVersion}"
  let state ← Std.Mutex.new { dir, opts, db }
  return { state }

/-! ### Certificates (§3.5) -/

private def insertCertificate (db : SQLite) (seq updatedAt : Nat) (key : String)
    (cert : StoredCertificate) : IO Unit := do
  let claim := cert.entry.claim
  execWith db
    ("INSERT OR REPLACE INTO certificates (" ++ certificateColumns ++
      ", hash_lower, fingerprint_lower) VALUES (" ++ placeholders 21 ++ ")")
    #[.text key, .count seq, .count updatedAt,
      .text claim.decl, .text claim.hash, .text claim.hasher, .text claim.repo,
      .text claim.commit, .text claim.toolchain, .text claim.asserted, .text claim.note,
      .text cert.entry.signature, .text cert.entry.key, .text cert.entry.fingerprint,
      .text cert.hints.issuer, .text cert.hints.keyVerifiedVia, .text cert.hints.origin,
      .text cert.fromPeer, .count cert.fetchedMs,
      .text claim.hash.toLower, .text cert.entry.fingerprint.toLower]

private def certificateAt (db : SQLite) (key : String) : IO (Option StoredCertificate) := do
  let row ← selectRow? db certificateColumns "certificates" "WHERE key = ?1"
    #[.text key] readCertificate
  return row.bind (·.value)

/--
Store an entry, resolving §3.5's collision.

The identity is `(fingerprint, hash, hasher)`; hashes from different hashers are
never comparable, so the hasher is part of the key rather than an attribute.  On
collision the later `asserted` wins, and a tie keeps what is already stored —
which is what makes gossiping the same set repeatedly converge instead of
oscillating between two nodes' copies.

The comparison is core's `Trust.laterThan` and is made in Lean, inside the
transaction that will do the write.  Asking SQL to order two RFC 3339 strings
would be a second implementation of a rule that has forked once already.
-/
def putCertificate (s : Store) (cert : StoredCertificate) : IO PutOutcome := do
  let claim := cert.entry.claim
  let key :=
    if cert.entry.fingerprint.isEmpty then attestedKey cert.hints.issuer claim.hash claim.hasher
    else certificateKey cert.entry.fingerprint claim.hash claim.hasher
  s.write fun db => do
    let existing ← certificateAt db key
    let outcome :=
      match existing with
      | none => PutOutcome.inserted
      | some old =>
        if Trust.laterThan claim.asserted old.entry.claim.asserted then .replaced else .kept
    if outcome == .kept then return outcome
    let (seq, updatedAt) ← alloc db
    insertCertificate db seq updatedAt key cert
    return outcome

/-- Withdraw a certificate from this node.  The row is gone, not tombstoned. -/
def deleteCertificate (s : Store) (fingerprint hash hasher : String) : IO Unit :=
  s.write fun db => do
    let stmt ← db sql!"DELETE FROM certificates WHERE key = {certificateKey fingerprint hash hasher}"
    stmt.exec

def getCertificate (s : Store) (fingerprint hash hasher : String) :
    IO (Option StoredCertificate) :=
  s.withDb (certificateAt · (certificateKey fingerprint hash hasher))

/-! ### Revocations (§6) -/

private def insertRevocation (db : SQLite) (seq updatedAt : Nat) (key : String)
    (rev : Trust.SignedRevocation) : IO Unit := do
  let r := rev.revocation
  execWith db
    ("INSERT OR REPLACE INTO revocations (" ++ revocationColumns ++
      ", hash_lower, fingerprint_lower) VALUES (" ++ placeholders 13 ++ ")")
    #[.text key, .count seq, .count updatedAt,
      .text r.fingerprint, .text r.hash, .text r.hasher, .text r.reason, .text r.revoked,
      .text rev.signature, .text rev.key, .text rev.fingerprint,
      .text r.hash.toLower, .text r.fingerprint.toLower]

private def revocationAt (db : SQLite) (key : String) : IO (Option Trust.SignedRevocation) := do
  let row ← selectRow? db revocationColumns "revocations" "WHERE key = ?1"
    #[.text key] readRevocation
  return row.bind (·.value)

/--
Store a withdrawal.

Kept whether or not the certificate it names has ever been seen (§6, rule 4):
the certificate may arrive by another path afterwards, and dropping the
revocation would resolve that race in favour of the assertion.  A later
`revoked` for the same triple supersedes an earlier one, again by core's
`Trust.laterThan`.
-/
def putRevocation (s : Store) (rev : Trust.SignedRevocation) : IO PutOutcome := do
  let r := rev.revocation
  let key := revocationKey r.fingerprint r.hash r.hasher
  s.write fun db => do
    let existing ← revocationAt db key
    let outcome :=
      match existing with
      | none => PutOutcome.inserted
      | some old => if Trust.laterThan r.revoked old.revocation.revoked then .replaced else .kept
    if outcome == .kept then return outcome
    let (seq, updatedAt) ← alloc db
    insertRevocation db seq updatedAt key rev
    return outcome

def getRevocation (s : Store) (fingerprint hash hasher : String) :
    IO (Option Trust.SignedRevocation) :=
  s.withDb (revocationAt · (revocationKey fingerprint hash hasher))

/--
§6.2 rule 2: is a certificate asserted at `asserted` suppressed?

A revocation suppresses exactly those certificates with the same triple whose
`asserted` is **not later** than `revoked`, by core's `Trust.notLaterThan`.
Rule 3 falls straight out of that: re-issuing afterwards asserts later, so it
reinstates by itself and needs no second message.
-/
def isRevoked (s : Store) (fingerprint hash hasher asserted : String) : IO Bool := do
  match ← s.getRevocation fingerprint hash hasher with
  | none => return false
  | some rev => return Trust.notLaterThan asserted rev.revocation.revoked

/-- Everything stored for a hash, with §6.2 applied unless asked otherwise. -/
def certificatesByHash (s : Store) (hash : String) (hasher : Option String := none)
    (includeRevoked : Bool := false) : IO (Array StoredCertificate) :=
  s.withDb fun db => do
    let wanted := hash.toLower
    let clause :=
      if hasher.isSome then "WHERE hash_lower = ?1 AND hasher = ?2 ORDER BY updated_at, seq"
      else "WHERE hash_lower = ?1 ORDER BY updated_at, seq"
    let binds := #[Val.text wanted] ++ (hasher.map (Val.text ·)).toArray
    let rows ← selectRows db certificateColumns "certificates" clause binds readCertificate
    let certificates := rows.filterMap (·.value)
    if includeRevoked then return certificates
    -- The withdrawals for this hash in one query, then §6.2 decided in Lean:
    -- the comparison is core's, and a revocation is matched by the very key it
    -- is filed under, which is §3.5's triple.
    let revocations ← selectRows db revocationColumns "revocations"
      "WHERE hash_lower = ?1" #[.text wanted] readRevocation
    let byKey := revocations.foldl
      (fun (m : Std.HashMap String Trust.SignedRevocation) row =>
        match row.value with
        | some rev => m.insert row.key rev
        | none => m) {}
    return certificates.filter fun cert =>
      let claim := cert.entry.claim
      match byKey.get? (revocationKey cert.entry.fingerprint claim.hash claim.hasher) with
      | some rev => !Trust.notLaterThan claim.asserted rev.revocation.revoked
      | none => true

/-- Everything signed by one key, §6.2 applied. -/
def certificatesByFingerprint (s : Store) (fingerprint : String) :
    IO (Array StoredCertificate) := do
  let rows ← s.withDb fun db =>
    selectRows db certificateColumns "certificates"
      "WHERE fingerprint_lower = ?1 ORDER BY updated_at, seq"
      #[.text fingerprint.toLower] readCertificate
  let mut out := #[]
  for cert in rows.filterMap (·.value) do
    let claim := cert.entry.claim
    if ← s.isRevoked cert.entry.fingerprint claim.hash claim.hasher claim.asserted then continue
    out := out.push cert
  return out

/-- Every certificate row, §6.2 not applied.  The caller decides what to hide. -/
def liveCertificates (s : Store) : IO (Array StoredCertificate) := do
  let rows ← s.withDb fun db =>
    selectRows db certificateColumns "certificates" "ORDER BY updated_at, seq" #[] readCertificate
  return rows.filterMap (·.value)

/--
Withdraw an account's own rows for a hash from this node.

Only what this node originated and only what that account issued: a copy that
arrived from a peer is not ours to take back, and a signed withdrawal (§6) is
the form that travels.  Returns how many rows were removed.

One statement, so the count and the deletion cannot disagree.  `from_peer = ''`
is `StoredCertificate.isLocal` and `hint_issuer` is the account, both of which
are columns rather than comparisons of time — nothing here is a protocol rule.
-/
def withdrawLocal (s : Store) (issuer hash : String) : IO Nat :=
  s.write fun db => do
    execWith db
      "DELETE FROM certificates WHERE from_peer = '' AND hint_issuer = ?1 AND hash_lower = ?2"
      #[.text issuer, .text hash.toLower]
    changed db

/-- Withdrawals matching a filter, for the bundle a query answers with. -/
def revocationsFor (s : Store) (hash : Option String := none) (hasher : Option String := none)
    (fingerprint : Option String := none) : IO (Array Trust.SignedRevocation) := do
  let opt : Option String → Val := fun
    | some v => .text v
    | none => .null
  let rows ← s.withDb fun db =>
    selectRows db revocationColumns "revocations"
      ("WHERE (?1 IS NULL OR hash_lower = ?1) AND (?2 IS NULL OR hasher = ?2) " ++
        "AND (?3 IS NULL OR fingerprint_lower = ?3) ORDER BY updated_at, seq")
      #[opt (hash.map (·.toLower)), opt hasher, opt (fingerprint.map (·.toLower))]
      readRevocation
  return rows.filterMap (·.value)

/-! ### Export (§4.1) -/

/--
Certificates in cursor order, for a peer catching up.

§6.2 is *not* applied here — revocations travel in the same bundle (§6, rule 4)
and the receiver applies them itself, which is what lets a withdrawal survive
being relayed by a node that never held the certificate it withdraws.
-/
def certificatesSince (s : Store) (since : String := "") (limit : Nat := 500) :
    IO (Page StoredCertificate) :=
  s.withDb (pageOf · certificateColumns "certificates" (Cursor.decode? since) limit readCertificate)

def revocationsSince (s : Store) (since : String := "") (limit : Nat := 500) :
    IO (Page Trust.SignedRevocation) :=
  s.withDb (pageOf · revocationColumns "revocations" (Cursor.decode? since) limit readRevocation)

/-! ### Peers (§5) -/

private def insertPeer (db : SQLite) (seq updatedAt : Nat) (peer : Peer) : IO Unit :=
  execWith db
    ("INSERT OR REPLACE INTO peers (" ++ peerColumns ++ ") VALUES (" ++ placeholders 10 ++ ")")
    #[.text (tupleKey [peer.url]), .count seq, .count updatedAt,
      .text peer.url, .text peer.name, .text peer.status.toString, .text peer.cursor,
      .count peer.lastSeenMs, .text peer.lastError, .count peer.addedMs]

/-- Record a peer verbatim, overwriting whatever was there.  The operator's word. -/
def putPeer (s : Store) (peer : Peer) : IO Unit := do
  let addedMs ← if peer.addedMs != 0 then pure peer.addedMs else nowMs
  s.write fun db => do
    let (seq, updatedAt) ← alloc db
    insertPeer db seq updatedAt { peer with addedMs }

def getPeer (s : Store) (url : String) : IO (Option Peer) :=
  s.withDb fun db => do
    let row ← selectRow? db peerColumns "peers" "WHERE key = ?1"
      #[.text (tupleKey [url])] readPeer
    return row.bind (·.value)

def listPeers (s : Store) (statuses : Array PeerStatus := #[]) : IO (Array Peer) := do
  let rows ← s.withDb fun db =>
    selectRows db peerColumns "peers" "ORDER BY updated_at, seq" #[] readPeer
  let all := rows.filterMap (·.value)
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

def forgetPeer (s : Store) (url : String) : IO Unit :=
  s.write fun db => do
    let stmt ← db sql!"DELETE FROM peers WHERE key = {tupleKey [url]}"
    stmt.exec

/-! ### Identities, keys, sessions, follows -/

private def insertIdentity (db : SQLite) (seq updatedAt : Nat) (identity : Identity) : IO Unit :=
  execWith db
    ("INSERT OR REPLACE INTO identities (" ++ identityColumns ++ ") VALUES (" ++
      placeholders 7 ++ ")")
    #[.text (tupleKey [identity.login]), .count seq, .count updatedAt,
      .text identity.login, .int identity.githubId, .text identity.avatarUrl,
      .count identity.createdMs]

def putIdentity (s : Store) (identity : Identity) : IO Unit := do
  let createdMs ← if identity.createdMs != 0 then pure identity.createdMs else nowMs
  s.write fun db => do
    let (seq, updatedAt) ← alloc db
    insertIdentity db seq updatedAt { identity with createdMs }

def getIdentity (s : Store) (login : String) : IO (Option Identity) :=
  s.withDb fun db => do
    let row ← selectRow? db identityColumns "identities" "WHERE key = ?1"
      #[.text (tupleKey [login])] readIdentity
    return row.bind (·.value)

/-- The account a GitHub id belongs to, whatever it currently calls itself. -/
def identityByGitHubId (s : Store) (githubId : Int) : IO (Option Identity) := do
  if githubId < 0 then return none
  let row ← s.withDb fun db =>
    selectRow? db identityColumns "identities"
      "WHERE github_id = ?1 ORDER BY updated_at, seq LIMIT 1" #[.int githubId] readIdentity
  return row.bind (·.value)

def listIdentities (s : Store) : IO (Array Identity) := do
  let rows ← s.withDb fun db =>
    selectRows db identityColumns "identities" "ORDER BY updated_at, seq" #[] readIdentity
  return rows.filterMap (·.value)

private def insertKey (db : SQLite) (seq updatedAt : Nat) (key : PublicKey) : IO Unit :=
  execWith db
    ("INSERT OR REPLACE INTO keys (" ++ keyColumns ++ ") VALUES (" ++ placeholders 8 ++ ")")
    #[.text (tupleKey [key.login, key.fingerprint.toLower]), .count seq, .count updatedAt,
      .text key.fingerprint.toLower, .text key.login, .text key.armored,
      .text key.verifiedVia, .count key.addedMs]

private def insertFollow (db : SQLite) (seq updatedAt : Nat) (follow : Follow) : IO Unit :=
  execWith db
    ("INSERT OR REPLACE INTO follows (" ++ followColumns ++ ") VALUES (" ++ placeholders 8 ++ ")")
    #[.text (tupleKey [follow.truster, follow.kind, follow.target]), .count seq, .count updatedAt,
      .text follow.truster, .text follow.target, .text follow.kind, .text follow.label,
      .count follow.addedMs]

/--
Follow a GitHub rename.

Identities, keys and follows are all filed under the login, because that is what
a certificate's hints and a trust list name.  A renamed account is still the
same account — its GitHub id has not moved — so the rows move with it rather
than the person losing their keys and their trust list to a change of name.

All of it in one transaction: an account that had lost its identity row but kept
its keys under the old login would be an account nobody can sign in to and whose
trust list still counts.  Each moved row takes a fresh `seq`, so a peer walking
the cursor sees the move.
-/
def renameIdentity (s : Store) (oldLogin newLogin : String) : IO Unit := do
  if oldLogin == newLogin then return ()
  let createdMs ← nowMs
  s.write fun db => do
    let existing ← selectRow? db identityColumns "identities" "WHERE key = ?1"
      #[.text (tupleKey [oldLogin])] readIdentity
    match existing.bind (·.value) with
    | none => return ()
    | some identity =>
    execWith db "DELETE FROM identities WHERE key = ?1" #[.text (tupleKey [oldLogin])]
    let (seq, updatedAt) ← alloc db
    let kept := if identity.createdMs != 0 then identity.createdMs else createdMs
    insertIdentity db seq updatedAt { identity with login := newLogin, createdMs := kept }
    let keys ← selectRows db keyColumns "keys" "WHERE login = ?1 ORDER BY updated_at, seq"
      #[.text oldLogin] readKey
    for row in keys do
      let some stored := row.value | continue
      execWith db "DELETE FROM keys WHERE key = ?1" #[.text row.key]
      let (seq, updatedAt) ← alloc db
      insertKey db seq updatedAt { stored with login := newLogin }
    let follows ← selectRows db followColumns "follows"
      "WHERE truster = ?1 ORDER BY updated_at, seq" #[.text oldLogin] readFollow
    for row in follows do
      let some follow := row.value | continue
      execWith db "DELETE FROM follows WHERE key = ?1" #[.text row.key]
      let (seq, updatedAt) ← alloc db
      insertFollow db seq updatedAt { follow with truster := newLogin }

/-- Register a public key against an account.  Nothing else is ever stored beside one. -/
def putKey (s : Store) (key : PublicKey) : IO Unit := do
  let addedMs ← if key.addedMs != 0 then pure key.addedMs else nowMs
  s.write fun db => do
    let (seq, updatedAt) ← alloc db
    insertKey db seq updatedAt { key with fingerprint := key.fingerprint.toLower, addedMs }

def keysForLogin (s : Store) (login : String) : IO (Array PublicKey) := do
  let rows ← s.withDb fun db =>
    selectRows db keyColumns "keys" "WHERE login = ?1 ORDER BY updated_at, seq"
      #[.text login] readKey
  return rows.filterMap (·.value)

/--
Any key this node has seen, wherever it saw it.

Falls back to the key a federated entry travelled with, marked `remote`: a
reader checking a relayed entry has a fingerprint and nothing else they could
have looked up, and that key is tied to nothing this node verified about an
account.
-/
def keyByFingerprint (s : Store) (fingerprint : String) : IO (Option PublicKey) :=
  s.withDb fun db => do
    let wanted := fingerprint.toLower
    let registered ← selectRow? db keyColumns "keys"
      "WHERE fingerprint = ?1 ORDER BY updated_at, seq LIMIT 1" #[.text wanted] readKey
    match registered.bind (·.value) with
    | some key => return some key
    | none =>
      let seen ← selectRow? db certificateColumns "certificates"
        "WHERE fingerprint_lower = ?1 AND key_armored <> '' ORDER BY updated_at, seq LIMIT 1"
        #[.text wanted] readCertificate
      match seen.bind (·.value) with
      | some cert => return some {
          fingerprint := wanted, login := cert.hints.issuer, armored := cert.entry.key,
          verifiedVia := "remote" }
      | none => return none

/--
Write down a credential.

Filed under the value itself, so that presenting it is a lookup rather than a
scan.  The comparison that *decides* anything is still `secureEqual` in
`TrustServer.Auth`: an index probe is a hint, not an authorisation.
-/
def putSession (s : Store) (session : Session) : IO Unit := do
  let createdMs ← if session.createdMs != 0 then pure session.createdMs else nowMs
  s.write fun db => do
    let (seq, updatedAt) ← alloc db
    let session := { session with createdMs }
    execWith db
      ("INSERT OR REPLACE INTO sessions (" ++ sessionColumns ++ ") VALUES (" ++
        placeholders 11 ++ ")")
      #[.text (tupleKey [session.token]), .count seq, .count updatedAt,
        .text session.token, .text session.id, .text session.kind.toString,
        .text session.login, .text session.name, .count session.createdMs,
        .count session.expiresMs, .count session.lastUsedMs]

/-- The row a presented value names, if there is one.  Expiry is the caller's to check. -/
def getSession (s : Store) (token : String) : IO (Option Session) :=
  s.withDb fun db => do
    let row ← selectRow? db sessionColumns "sessions" "WHERE key = ?1"
      #[.text (tupleKey [token])] readSession
    return row.bind (·.value)

/-- A credential by its public id, which is what a listing hands out. -/
def sessionById (s : Store) (id : String) : IO (Option Session) := do
  if id.isEmpty then return none
  let row ← s.withDb fun db =>
    selectRow? db sessionColumns "sessions" "WHERE id = ?1 ORDER BY updated_at, seq LIMIT 1"
      #[.text id] readSession
  return row.bind (·.value)

def listSessions (s : Store) (login : String) (kind : SessionKind) : IO (Array Session) := do
  let rows ← s.withDb fun db =>
    selectRows db sessionColumns "sessions"
      "WHERE login = ?1 AND kind = ?2 ORDER BY updated_at, seq"
      #[.text login, .text kind.toString] readSession
  return rows.filterMap (·.value)

def deleteSession (s : Store) (token : String) : IO Unit :=
  s.write fun db => do
    let stmt ← db sql!"DELETE FROM sessions WHERE key = {tupleKey [token]}"
    stmt.exec

/--
Drop everything that has died, so an OAuth round trip cannot grow the store forever.

`Session.alive` is `expiresMs == 0 || now < expiresMs`, so dead is
`expires_ms <> 0 AND now >= expires_ms`.  These are the credential's own
lifetime, not a protocol ordering: nothing in §3 or §6 is decided here.
-/
def expireSessions (s : Store) : IO Nat := do
  let now ← nowMs
  s.write fun db => do
    execWith db "DELETE FROM sessions WHERE expires_ms <> 0 AND ?1 >= expires_ms" #[.count now]
    changed db

def putFollow (s : Store) (follow : Follow) : IO Unit := do
  let addedMs ← if follow.addedMs != 0 then pure follow.addedMs else nowMs
  s.write fun db => do
    let (seq, updatedAt) ← alloc db
    insertFollow db seq updatedAt { follow with addedMs }

def deleteFollow (s : Store) (truster kind target : String) : IO Unit :=
  s.write fun db => do
    let stmt ← db sql!"DELETE FROM follows WHERE key = {tupleKey [truster, kind, target]}"
    stmt.exec

def listFollows (s : Store) (truster : String) : IO (Array Follow) := do
  let rows ← s.withDb fun db =>
    selectRows db followColumns "follows" "WHERE truster = ?1 ORDER BY updated_at, seq"
      #[.text truster] readFollow
  return rows.filterMap (·.value)

/-! ### Housekeeping -/

/-- §2's `counts`: live certificates, and the peers this node queries. -/
def counts (s : Store) : IO (Nat × Nat) := do
  let certificates ← s.withDb fun db => do
    let stmt ← db.prepare "SELECT COUNT(*) FROM certificates"
    return (← first? stmt (num · 0)).getD 0
  let peers ← s.queriedPeers
  return (certificates, peers.size)

/--
Give the file back the space its dead rows are holding.

The log meant something quite different by this word: it rewrote a file that
held every version of every row.  A row is now updated in place, so there is no
superseded version to drop; what is left is SQLite's own bookkeeping, which is
what `wal_checkpoint` and `VACUUM` reclaim.  Neither may run inside a
transaction, so this is deliberately not wrapped in one.
-/
def compact (s : Store) : IO Unit :=
  s.withDb fun db => do
    db.exec "PRAGMA wal_checkpoint(TRUNCATE)"
    db.exec "VACUUM"

/--
How many certificate rows there are, twice.

The log returned records-on-disk and live-rows, and the gap between them was the
thing compaction closed.  There is no gap now: one row per key is all there ever
is, so both halves are the same number.  Kept as a pair because it is a public
signature, and because a caller asking "how much is superseded?" should get the
true answer, which is none.
-/
def certificateLogSize (s : Store) : IO (Nat × Nat) := do
  let (certificates, _) ← s.counts
  return (certificates, certificates)

/--
Push the write-ahead log into the database file.

A commit is already durable to whatever `Options.fsync` selected before it
returns; this is only about where the bytes sit.  Nothing needs closing, because
closing is the process exiting.
-/
def flush (s : Store) : IO Unit :=
  s.withDb fun db => db.exec "PRAGMA wal_checkpoint(PASSIVE)"

end Store

end TrustServer
