import Std.Http
import TrustServer.Store

/-!
# Configuration

Everything the process reads from its environment, in one place, resolved once
into a value.

This is a port of `server/src/config.ts`.  Scattered environment reads make it
impossible to answer "what does this node do" without grepping and — more
practically — impossible to run two nodes in one test process, which is exactly
what a federation test needs to do.

The one deliberate divergence from the TypeScript is `store`: there is no
`pg`/`sqlite` choice here because there is no SQL here.  A store is a directory
of append-only logs (see `TrustServer/Store.lean` for why), so the setting that
replaces `DATABASE_URL` and `SQLITE_PATH` is a path.
-/

namespace TrustServer

open Std.Http (Config)

/-! ## Reading the environment -/

/-- A number, or the default when it is unset, empty, unparseable or negative. -/
def envNat (env : String → Option String) (name : String) (fallback : Nat) : Nat :=
  match env name with
  | none => fallback
  | some "" => fallback
  | some raw => raw.trimAscii.toString.toNat?.getD fallback

/-- `true`, `1` and `yes` are true; anything else present is false. -/
def envBool (env : String → Option String) (name : String) (fallback : Bool) : Bool :=
  match env name with
  | none => fallback
  | some "" => fallback
  | some raw => raw == "true" || raw == "1" || raw == "yes"

def envString (env : String → Option String) (name : String) (fallback : String := "") : String :=
  (env name).getD fallback

/-- A comma-separated list, trimmed, with the empty entries dropped. -/
def envList (env : String → Option String) (name : String) : Array String :=
  ((env name).getD "").splitOn ","
    |>.map (·.trimAscii.toString)
    |>.filter (!·.isEmpty)
    |>.toArray

/-- Trailing slashes off, so that a URL compares equal to itself (§5.2). -/
def stripTrailingSlashes (url : String) : String :=
  String.ofList (url.toList.reverse.dropWhile (· == '/')).reverse

/-! ## The policy of §8 -/

/--
The limits of §8, all of them defences against a peer that is hostile or merely
broken — and the two are not distinguishable from the outside.

The defaults are the ones the table in §8 documents, and a conforming node
enforces at least these.
-/
structure Policy where
  /-- Fan-out is exponential in depth (§7.1). -/
  maxDepth : Nat := 2
  /-- Bounds a single response; the sender says `complete: false` when it bites. -/
  maxEntries : Nat := 500
  /-- A peer's response is untrusted input. -/
  maxResponseBytes : Nat := 2 * 1024 * 1024
  /-- One slow peer must not own the request (§7.2). -/
  peerTimeoutMs : Nat := 4000
  /-- Bounds the whole fan-out, in wall-clock time rather than in peers. -/
  queryBudgetMs : Nat := 8000
  /-- How stale a cached remote answer may be (§7.3). -/
  remoteTtlS : Nat := 300
  /-- Bounds the relay chain (§7.1). -/
  maxViaLength : Nat := 8
  /-- Whether a newly discovered peer is queried, or only recorded (§5.1). -/
  autodiscover : Bool := false
  /-- Allow `http` and private addresses (§5.4).  For local mode and tests only. -/
  allowPrivate : Bool := false
  deriving Inhabited, Repr

/-! ## The configuration -/

structure GitHubApp where
  clientId : String := ""
  clientSecret : String := ""
  deriving Inhabited, Repr

structure ServerConfig where
  port : Nat := 8080
  /-- This node's own externally reachable base URL; its name in `via` chains (§7.1). -/
  publicUrl : String := ""
  /-- Where the frontend runs, and the one origin allowed to send cookies. -/
  appUrl : String := ""
  name : String := ""
  /--
  Local mode (§9): one user, no OAuth, no public surface.

  Spelled `localMode` rather than `local`, which the TypeScript calls it,
  because `local` is a Lean keyword and a field that has to be written
  `«local»` at every use is worse than a field with a longer name.
  -/
  localMode : Bool := false
  /--
  Bind every interface rather than loopback.

  Off by default, because a node that is reachable before its operator said so
  is the wrong default for something that accepts POSTs from strangers.  A
  container turns it on: there the container boundary is the isolation, and
  binding loopback inside one makes the node unreachable through its own
  published port — which is a confusing way to be safe.
  -/
  bindAll : Bool := false
  /-- The directory the append-only logs live in. -/
  storeDir : String := ""
  /-- Whether every append is `fdatasync`ed before it returns. -/
  storeFsync : Bool := true
  sessionSecret : String := ""
  cookieSecure : Bool := false
  github : GitHubApp := {}
  /-- Peers the operator configured; they start in `seed` (§5.1). -/
  seeds : Array String := #[]
  /--
  Bearer token for the handful of operations that are the operator's, not a
  user's: promoting a peer, blocking one, forcing a pull.  Unset means those
  endpoints are closed rather than open — a federation control plane that
  defaults to reachable is not one.
  -/
  adminToken : String := ""
  policy : Policy := {}
  deriving Inhabited, Repr

namespace ServerConfig

/-- `~/.local/share/trust/store`, or under `$XDG_DATA_HOME` when that is set. -/
def defaultStoreDir (env : String → Option String) : String :=
  let base :=
    match env "XDG_DATA_HOME" with
    | some d => if d.isEmpty then none else some d
    | none => none
  match base with
  | some d => s!"{d}/trust/store"
  | none =>
    match env "HOME" with
    | some home => if home.isEmpty then "./trust-store" else s!"{home}/.local/share/trust/store"
    | none => "./trust-store"

/-- Resolve a configuration from an environment given as a function. -/
def ofEnv (env : String → Option String) : ServerConfig :=
  let localMode := envBool env "TRUST_LOCAL" false
  let port := envNat env "PORT" (if localMode then 8090 else 8080)
  {
    port
    publicUrl := stripTrailingSlashes
      (envString env "PUBLIC_URL" (if localMode then s!"http://127.0.0.1:{port}" else ""))
    appUrl := stripTrailingSlashes (envString env "APP_URL")
    name := envString env "NODE_NAME" (if localMode then "local" else "")
    localMode
    bindAll := envBool env "TRUST_BIND_ALL" false
    storeDir := envString env "TRUST_STORE_DIR" (defaultStoreDir env)
    storeFsync := envBool env "TRUST_STORE_FSYNC" true
    -- In local mode nothing is exposed and there is nobody to forge a session
    -- against, so a generated secret beats refusing to start over a missing one.
    sessionSecret := envString env "SESSION_SECRET"
    cookieSecure := envBool env "COOKIE_SECURE" false
    github := {
      clientId := envString env "GITHUB_CLIENT_ID"
      clientSecret := envString env "GITHUB_CLIENT_SECRET" }
    seeds := envList env "FEDERATION_SEEDS"
    adminToken := envString env "ADMIN_TOKEN"
    policy := {
      maxDepth := envNat env "FEDERATION_MAX_DEPTH" 2
      maxEntries := envNat env "FEDERATION_MAX_ENTRIES" 500
      maxResponseBytes := envNat env "FEDERATION_MAX_RESPONSE_BYTES" (2 * 1024 * 1024)
      peerTimeoutMs := envNat env "FEDERATION_PEER_TIMEOUT_MS" 4000
      queryBudgetMs := envNat env "FEDERATION_QUERY_BUDGET_MS" 8000
      remoteTtlS := envNat env "FEDERATION_REMOTE_TTL_S" 300
      maxViaLength := envNat env "FEDERATION_MAX_VIA" 8
      autodiscover := envBool env "FEDERATION_AUTODISCOVER" false
      -- Local mode pulls from other things on the same machine, so the private
      -- address rule would forbid exactly its normal use.  A public deployment
      -- has to opt in deliberately.
      allowPrivate := envBool env "FEDERATION_ALLOW_PRIVATE" localMode }
  }

/-- Read the real process environment. -/
def load : IO ServerConfig := do
  let mut seen : Std.HashMap String (Option String) := {}
  -- `IO.getEnv` is IO, and `ofEnv` is not, so the variables it can ask for are
  -- looked up first.  The list is the whole configuration surface: if a name is
  -- missing from it, `ofEnv` will see it as unset, which is the failure mode
  -- that a single list in one place is meant to prevent.
  let names := #[
    "TRUST_LOCAL", "TRUST_BIND_ALL", "PORT", "PUBLIC_URL", "APP_URL", "NODE_NAME",
    "TRUST_STORE_DIR", "TRUST_STORE_FSYNC", "XDG_DATA_HOME", "HOME",
    "SESSION_SECRET", "COOKIE_SECURE", "GITHUB_CLIENT_ID", "GITHUB_CLIENT_SECRET",
    "FEDERATION_SEEDS", "ADMIN_TOKEN",
    "FEDERATION_MAX_DEPTH", "FEDERATION_MAX_ENTRIES", "FEDERATION_MAX_RESPONSE_BYTES",
    "FEDERATION_PEER_TIMEOUT_MS", "FEDERATION_QUERY_BUDGET_MS", "FEDERATION_REMOTE_TTL_S",
    "FEDERATION_MAX_VIA", "FEDERATION_AUTODISCOVER", "FEDERATION_ALLOW_PRIVATE"]
  for name in names do
    seen := seen.insert name (← IO.getEnv name)
  return ofEnv (seen.get? · |>.join)

/--
Refuse to start misconfigured rather than fail confusingly on first use.

Local mode needs almost none of this: there is no OAuth round trip to get wrong
and no origin to mismatch, and demanding a GitHub app before someone can keep
their own judgements in their own database would be absurd.
-/
def problems (c : ServerConfig) : Array String := Id.run do
  let mut out := #[]
  if c.storeDir.isEmpty then
    out := out.push "TRUST_STORE_DIR is not set and no default could be derived"
  if !c.localMode then
    if c.sessionSecret.length < 32 then
      out := out.push "SESSION_SECRET must be at least 32 characters (openssl rand -hex 32)"
    if c.github.clientId.isEmpty then out := out.push "GITHUB_CLIENT_ID is not set"
    if c.github.clientSecret.isEmpty then out := out.push "GITHUB_CLIENT_SECRET is not set"
    if c.publicUrl.isEmpty then out := out.push "PUBLIC_URL is not set"
  if !c.publicUrl.isEmpty &&
      !(c.publicUrl.startsWith "http://" || c.publicUrl.startsWith "https://") then
    out := out.push "PUBLIC_URL must be an absolute http(s) URL"
  return out

/-- The store options this configuration implies. -/
def storeOptions (c : ServerConfig) : Options := { fsync := c.storeFsync }

/--
The §8 limits, mapped onto `Std.Http.Config` where the two are talking about the
same thing.

**What maps.**

* `maxResponseBytes` → `maxBodySize`.  §8 states it as a bound on a *peer's*
  response, which is the client half of federation; the same number is the right
  bound on an inbound `POST /api/import` body, because that is the same untrusted
  bundle arriving by the other door.  Setting it here means a stranger cannot
  fill this node's disk with one request, which §4.2 is about.
* `maxEntries` → `maxHeaders` is **not** a mapping and is not made: they are
  both counts, of unrelated things.  Listed here only because it is the mapping
  someone will be tempted to write.

**What does not map, and why.**

* `maxDepth`, `maxEntries`, `maxViaLength`, `remoteTtlS` are federation policy.
  They constrain what this node *asks* and what it *answers*, and the HTTP
  server has no notion of either.  They are enforced by the federation code.
* `peerTimeoutMs` and `queryBudgetMs` bound this node's own *outbound* requests.
  `Config.headerTimeout` and `Config.lingeringTimeout` look similar and are the
  opposite direction: they bound how long this node will wait on a *client*.
  Mapping one onto the other would silently make a slow reader look like a slow
  peer, so neither is touched and both keep their `Std.Http` defaults.
* `autodiscover` and `allowPrivate` are decisions about addresses and peers, and
  nothing in an HTTP server configuration corresponds to them at all.
-/
def httpConfig (c : ServerConfig) : Config :=
  { maxBodySize := c.policy.maxResponseBytes }

end ServerConfig

end TrustServer
