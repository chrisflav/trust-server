import Lean
import Std.Http
import Std.Data.HashMap
import Trust.Cert
import Trust.Federation
import Trust.Net
import TrustServer.Config
import TrustServer.Store

/-!
# Talking to another node

Everything a peer sends is untrusted input, including its size, its shape and
how long it takes to arrive.  So every request here is bounded three ways — a
deadline (§8's `peerTimeoutMs`), a byte cap (§8's `maxResponseBytes`) and a
refusal to follow redirects — and every response is parsed defensively: a peer
that answers with something unrecognised loses the exchange rather than the
node.

All of it goes out through `Trust.Net`, which is not a stylistic choice.
`Net.check` performs §5.4 and hands back a `Pinned` carrying the address it
approved; `Net.get` takes that `Pinned` and sends the request to *that address*.
There is no function here that takes a hostname, which is what keeps the DNS
rebinding §5.4 documents from reopening: a second resolution is not something
this file is able to ask for.
-/

namespace TrustServer
namespace Federation
namespace Client

open Lean (Json toJson fromJson?)

/-- §8's limits, as far as they bound one outbound request. -/
def netPolicy (policy : Policy) (timeoutMs : Option Nat := none) : Trust.Net.Policy where
  allowPrivate := policy.allowPrivate
  maxResponseBytes := policy.maxResponseBytes
  timeoutMs := timeoutMs.getD policy.peerTimeoutMs

/-- A peer's words, cut to something an error message can hold. -/
def brief (s : String) (limit : Nat := 160) : String :=
  let s := (s.trimAscii.toString.replace "\n" " ").replace "\r" " "
  if s.length > limit then (s.take limit).toString ++ "…" else s

/-- A query string, with every value percent-encoded and empty ones dropped. -/
private def query (pairs : List (String × String)) : String :=
  let parts := pairs.filterMap fun (k, v) =>
    if v.isEmpty then none
    else some s!"{k}={toString (Std.Http.URI.EncodedQueryParam.encode v)}"
  match parts with
  | [] => ""
  | parts => "?" ++ String.intercalate "&" parts

/--
A JSON GET against a peer, with §5.4 applied to the base URL first.

The base is checked and pinned; the path — endpoint and parameters — is appended
afterwards, because §5.4 is about *where* the request goes and a query string
does not change that.  Checking the whole URL instead would refuse every
federated GET the moment it had a parameter.
-/
def fetchJson (base path : String) (policy : Policy) (timeoutMs : Option Nat := none) :
    IO (Except String Json) := do
  let net := netPolicy policy timeoutMs
  match ← Trust.Net.check base net with
  | .error why => return .error s!"{base}: {why}"
  | .ok pinned =>
    match ← Trust.Net.get pinned path net with
    | .error why => return .error s!"could not reach {base}{path}: {brief why}"
    | .ok response =>
      if response.status != 200 then
        return .error s!"{base}{path} answered {response.status}: {brief response.body}"
      match Json.parse response.body with
      | .error _ => return .error s!"{base}{path} did not answer with JSON"
      | .ok value => return .ok value

/--
§2's descriptor, and the one field whose absence is fatal.

A receiver that does not recognise the version must not proceed, so an
unrecognised `protocol` is an error here rather than something the caller is
trusted to check.
-/
def fetchDescriptor (base : String) (policy : Policy) :
    IO (Except String Trust.Federation.Descriptor) := do
  match ← fetchJson base "/api/federation" policy with
  | .error why => return .error why
  | .ok value =>
    match fromJson? (α := Trust.Federation.Descriptor) value with
    | .error _ => return .error s!"{base} did not answer with a node descriptor"
    | .ok descriptor =>
      if !descriptor.recognised then
        return .error
          s!"{base} speaks {brief descriptor.protocol 40}, and this node speaks {Trust.Federation.protocolVersion}"
      return .ok descriptor

/--
§4.4's hints, taken from an entry as it arrived.

Carried for display and never believed: nothing downstream of this lets a hint
affect acceptance, ordering or trust.  The lengths are a bound on what a peer
can make this node store per entry, not a judgement about content.
-/
def hintsOf (raw : Json) (origin : String) : Hints :=
  let hints := (raw.getObjVal? "hints").toOption.getD (Json.mkObj [])
  let field (name : String) (limit : Nat) : String :=
    let value := (hints.getObjValAs? String name).toOption.getD ""
    (value.take limit).toString
  let stated := field "origin" 300
  { issuer := field "issuer" 100
    keyVerifiedVia := field "keyVerifiedVia" 20
    -- A bundle that says where it came from names the origin of every entry in
    -- it that does not name its own.
    origin := if stated.isEmpty then origin else stated }

/--
A bundle as it arrived: the part core can decide about, plus what it cannot.

The hints travel beside the bundle rather than inside it because `Trust.Entry`
is what a signature covers and a hint is not; keeping them apart is what stops
a hint from ever reaching `acceptEntry`.
-/
structure Arriving where
  bundle : Trust.Bundle
  /-- §4.4's hints, by `(fingerprint, hash, hasher)`, for the entries that survive. -/
  hints : Std.HashMap String Hints := {}
  /--
  Entries that were not §3.3 entries at all.

  Refused before any crypto, and counted rather than dropped silently: §4.2 says
  rejections are reported, and an unsigned entry — which is what §3.1 forbids
  federating — arrives here rather than at `acceptEntry`, because an entry with
  no `signature` field does not parse into one.
  -/
  unreadable : Nat := 0
  deriving Inhabited

/--
Shape-check a bundle.  Its contents are checked one entry at a time, later.

`protocol` is required to be one we recognise, exactly as in §2: a bundle in a
dialect this node does not speak is not a bundle it may take entries out of.
-/
def parseBundle (value : Json) : Except String Arriving := do
  let protocol := (value.getObjValAs? String "protocol").toOption.getD ""
  if protocol != Trust.Federation.protocolVersion then
    throw s!"the bundle says protocol {brief protocol 40}, and this node speaks {Trust.Federation.protocolVersion}"
  let origin := (value.getObjValAs? String "origin").toOption.getD ""
  let array (name : String) : Array Json :=
    ((value.getObjVal? name).bind Json.getArr?).toOption.getD #[]
  let mut entries : Array Trust.Entry := #[]
  let mut hints : Std.HashMap String Hints := {}
  let mut unreadable := 0
  for raw in array "entries" do
    match fromJson? (α := Trust.Entry) raw with
    | .error _ => unreadable := unreadable + 1
    | .ok entry =>
      hints := hints.insert
        (certificateKey entry.fingerprint entry.claim.hash entry.claim.hasher)
        (hintsOf raw origin)
      entries := entries.push entry
  let mut revocations : Array Trust.SignedRevocation := #[]
  for raw in array "revocations" do
    match fromJson? (α := Trust.SignedRevocation) raw with
    | .error _ => unreadable := unreadable + 1
    | .ok revocation => revocations := revocations.push revocation
  return {
    bundle := {
      protocol, origin, entries, revocations
      cursor := (value.getObjValAs? String "cursor").toOption.getD ""
      -- Absent means complete: a sender that truncates has to say so, and a
      -- receiver that assumed the other way would re-fetch for ever.
      complete := (value.getObjValAs? Bool "complete").toOption.getD true }
    hints, unreadable }

/-- §4.1: a page of a peer's export, resumed from `since`. -/
def fetchBundle (base since : String) (policy : Policy) (timeoutMs : Option Nat := none) :
    IO (Except String Arriving) := do
  let path := "/api/certificates/export" ++
    query [("since", since), ("limit", toString policy.maxEntries)]
  match ← fetchJson base path policy timeoutMs with
  | .error why => return .error why
  | .ok value =>
    match parseBundle value with
    | .error why => return .error s!"{base}: {why}"
    | .ok arriving => return .ok arriving

/-- §7's question, as one node asks it of another. -/
structure PeerQuestion where
  hash : String := ""
  hasher : String := ""
  fingerprint : String := ""
  /-- How many further hops this may travel; §7.1's `depth - 1`. -/
  depth : Nat := 0
  /-- §7.1's chain, ours already appended. -/
  via : Array String := #[]
  deriving Inhabited

/--
Ask a peer the question we were asked, one hop shallower.

The answer is requested as a bundle rather than in the peer's own response
shape, so that a relayed entry is checked by exactly the rules an imported one
is.  A node should not have two notions of what it will believe.
-/
def queryPeer (base : String) (question : PeerQuestion) (policy : Policy)
    (timeoutMs : Option Nat := none) : IO (Except String Arriving) := do
  let path := "/api/certificates" ++ query [
    ("format", "bundle"), ("depth", toString question.depth),
    ("hash", question.hash), ("hasher", question.hasher),
    ("fingerprint", question.fingerprint),
    ("via", String.intercalate "," question.via.toList)]
  match ← fetchJson base path policy timeoutMs with
  | .error why => return .error why
  | .ok value =>
    match parseBundle value with
    | .error why => return .error s!"{base}: {why}"
    | .ok arriving => return .ok arriving

end Client
end Federation
end TrustServer
