import Std.Http
import Std.Http.Server
import Std.Async
import Lean
import Trust.Cert
import Trust.Federation
import TrustServer.Http
import TrustServer.Auth

/-!
# The certificate routes

Publishing, reading, exporting, importing, withdrawing, and the trust list.

## The rules live in the core library

Nothing in this file decides whether an entry is acceptable or whether a
withdrawal bites.  §3.4 is `Trust.Federation.acceptEntry`, §6 is
`acceptRevocation`, a whole bundle is `checkBundle`, and §6.2's suppression is
`Store.isRevoked`.  That is the entire point of the rewrite: `README.md` says
`trust cert verify-bundle` "repeats, locally, precisely the check the server
claims to have done", and the only way for that sentence to stay true is for the
server and the CLI to call the same code.  A second implementation of §3.4
living here would be a copy to keep honest, and it would drift.

## What a reader gets back

Every certificate is returned with `canonical` — the exact bytes that were
signed — beside the signature and the key.  A tool whose subject is trust should
not ask to be taken at its word: `assurance` is this node's opinion, and a
reader who repeats the check needs never have to reconstruct what was signed.

## Delegation

`GET /api/certificates` accepts `depth` and **currently ignores it**: this node
answers from its own store.  Asking peers is §7 and belongs with the rest of
federation; the parameter is accepted rather than rejected so that a client
written against a node that does delegate keeps working, and `askedPeers: 0`
says truthfully that nobody was asked.
-/

open Std Std.Http Std.Async Std.Net
open Lean (Json ToJson FromJson toJson fromJson?)

namespace TrustServer

namespace Routes

/-! ## Rendering -/

/-- Absent is `null`, not `""`: the frontend types these `string | null`. -/
private def orNull (s : String) : Json := if s.isEmpty then Json.null else Json.str s

/--
A certificate as §7.4 has it.

`verifiedHere` records that this node applied §3.4 — it is this node's word, and
a reader is expected to repeat the check rather than take it, which is what
`canonical` and `key` are there for.
-/
def certificateJson (cert : StoredCertificate) (me avatarUrl : String) : Json :=
  Json.mkObj [
    ("claim", toJson cert.entry.claim),
    ("canonical", Json.str cert.entry.claim.canonical),
    ("signature", orNull cert.entry.signature),
    ("key", orNull cert.entry.key),
    ("fingerprint", orNull cert.entry.fingerprint),
    ("assurance", Json.str cert.assurance),
    ("issuer", Json.str cert.hints.issuer),
    ("avatarUrl", Json.str avatarUrl),
    ("keyVerifiedVia", orNull cert.hints.keyVerifiedVia),
    ("provenance", Json.mkObj [
      ("local", Json.bool cert.isLocal),
      ("origin", Json.str (if cert.hints.origin.isEmpty then me else cert.hints.origin)),
      ("fromPeer", Json.str cert.fromPeer),
      ("verifiedHere", Json.bool (cert.assurance == "signed")),
      ("fetchedAt",
        if cert.fetchedMs == 0 then Json.null else Json.str (Auth.isoOfMs cert.fetchedMs))])]

/--
An entry as §3.3 has it, hints included.

Built by hand rather than through `ToJson Trust.Entry`, which has no hints
field: §4.4's hints are what carries an account name across a boundary where
nothing can check one, and dropping them would leave a receiver with a
fingerprint and nothing to display beside it.
-/
def entryJson (cert : StoredCertificate) (origin : String) : Json :=
  Json.mkObj [
    ("claim", toJson cert.entry.claim),
    ("signature", Json.str cert.entry.signature),
    ("key", Json.str cert.entry.key),
    ("fingerprint", Json.str cert.entry.fingerprint),
    ("hints", Json.mkObj [
      ("issuer", Json.str cert.hints.issuer),
      ("keyVerifiedVia", Json.str
        (if cert.hints.keyVerifiedVia.isEmpty then "self" else cert.hints.keyVerifiedVia)),
      ("origin", Json.str (if cert.hints.origin.isEmpty then origin else cert.hints.origin))])]

/-- Signed first, then most recently asserted first: what a reader wants at the top. -/
private def ordered (rows : Array StoredCertificate) : Array StoredCertificate :=
  rows.qsort fun a b =>
    if a.assurance != b.assurance then a.assurance == "signed"
    else Trust.laterThan a.entry.claim.asserted b.entry.claim.asserted

/-- Avatars by login, so a listing can show one without a lookup per row. -/
private def avatars (app : App) : IO (Std.HashMap String String) := do
  let identities ← app.store.listIdentities
  return identities.foldl (fun m i => m.insert i.login i.avatarUrl) {}

/-! ## Liveness -/

/--
`GET /api/health`.

Reports what the store actually holds rather than a constant `true`, so that a
green health check means the log was opened and indexed and not merely that a
process is listening.
-/
private def health (app : App) (_req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let (certificates, peers) ← app.store.counts
  json Response.ok (Json.mkObj [
    ("ok", Json.bool true),
    ("name", Json.str app.config.name),
    ("certificates", toJson certificates),
    ("peers", toJson peers)])

/-! ## §2 The node descriptor -/

/-- The host part of a URL, for a node that was never given a name. -/
private def hostOf (url : String) : String :=
  let withoutScheme :=
    if url.startsWith "https://" then (url.drop 8).toString
    else if url.startsWith "http://" then (url.drop 7).toString
    else url
  (withoutScheme.splitOn "/").headD withoutScheme

/--
`GET /api/federation`, the descriptor of §2.

`url` is this node's own canonical, externally reachable base URL — the value a
peer checks against the URL it was handed (§5.2).  Reporting anything else,
including the address the request happened to arrive on, is what turns a node
into a probe for whoever asked.
-/
private def federation (app : App) (_req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let (certificates, peers) ← app.store.counts
  let descriptor : Trust.Federation.Descriptor := {
    url := app.config.publicUrl
    name :=
      if !app.config.name.isEmpty then app.config.name
      else if !app.config.publicUrl.isEmpty then hostOf app.config.publicUrl
      else "trust"
    software := "trust-server/0.1.0"
    policy := {
      maxDepth := app.config.policy.maxDepth
      maxEntries := app.config.policy.maxEntries
      autodiscover := app.config.policy.autodiscover }
    certificates, peers }
  json Response.ok (toJson descriptor)

/-! ## Publishing -/

/--
`POST /api/certificates`.

A signature is optional but is the whole point.  Signed, the entry goes through
§3.4 exactly as a federated one does — the same function, so a certificate
published here and one imported from a peer have been held to the same standard.
Unsigned, the row is only this server's word that a signed-in account said
something: it is marked `attested`, and it never leaves the node (§3.1).
-/
private def publish (app : App) (req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Auth.withIdentity app req fun identity => do
    let .ok body ← bodyJson app req | return ← badRequest "expected a JSON body"
    let .ok claimJson := body.getObjVal? "claim" | return ← badRequest "claim must be an object"
    let .ok claim := fromJson? (α := Trust.Claim) claimJson |
      return ← badRequest "claim must be an object with all eight fields"
    let signature := (body.getObjValAs? String "signature").toOption.getD ""
    let origin := app.config.publicUrl
    if signature.isEmpty then
      -- §3.4 rule 1 applies to an attested row too.  It is the only rule that
      -- can apply, and a store full of unparseable claims helps nobody.
      match Trust.Federation.wellFormed claim with
      | .error why => badRequest why
      | .ok _ =>
        let _ ← app.store.putCertificate {
          entry := { claim, signature := "", key := "", fingerprint := "" }
          hints := { issuer := identity.login, origin } }
        json Response.ok (Json.mkObj [
          ("ok", Json.bool true), ("assurance", Json.str "attested")])
    else
      let keys ← app.store.keysForLogin identity.login
      if keys.isEmpty then
        return ← badRequest "signature did not verify: no public key to check against"
      -- Every key the account registered is offered, and the first that accepts
      -- the entry under §3.4 is the one it was signed with.  Which key signed is
      -- a fact about the signature, not something the client gets to assert.
      let mut refusal := "no key of yours accepted it"
      let mut accepted : Option (Trust.Entry × PublicKey) := none
      for key in keys do
        if accepted.isSome then continue
        let entry : Trust.Entry :=
          { claim, signature, key := key.armored, fingerprint := key.fingerprint }
        match ← Trust.Federation.acceptEntry entry app.verifier with
        | .ok _ => accepted := some (entry, key)
        | .error rejection => refusal := rejection.describe
      match accepted with
      | none => badRequest s!"signature did not verify: {refusal}"
      | some (entry, key) =>
        let _ ← app.store.putCertificate {
          entry
          hints := { issuer := identity.login, keyVerifiedVia := key.verifiedVia, origin } }
        json Response.ok (Json.mkObj [
          ("ok", Json.bool true), ("assurance", Json.str "signed")])

/--
`DELETE /api/certificates/:hash`.

Hides the row here, which is all it can do: a copy that has already travelled is
not this server's to take back.  A signed revocation is the form that federates,
and the answer says so rather than letting somebody believe otherwise.
-/
private def withdraw (app : App) (req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Auth.withIdentity app req fun identity => do
    let hash := Auth.pathTail req "/api/certificates/"
    let removed ← app.store.withdrawLocal identity.login hash
    json Response.ok (Json.mkObj [
      ("ok", Json.bool true), ("withdrawn", toJson removed),
      ("note", Json.str
        "withdrawn here; publish a signed revocation to withdraw it everywhere")])

/-! ## Reading -/

/--
`GET /api/certificates?hash=&hasher=&fingerprint=&depth=`.

Answered from this node's store, with §6.2 applied — a suppressed certificate is
not returned at all.  `format=bundle` is the same answer in the shape a peer and
the CLI expect, which is how a relayed entry ends up checked by exactly the same
rules as an imported one.

`depth` is read and ignored; see the note at the top of this file.
-/
private def certificates (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let hash := Auth.query req "hash"
  let hasher := Auth.query req "hasher"
  let fingerprint := Auth.query req "fingerprint"
  if hash.isNone && fingerprint.isNone then
    return ← badRequest "hash or fingerprint is required"
  let rows ← match hash, fingerprint with
    | some h, _ => app.store.certificatesByHash h hasher
    | none, some f => app.store.certificatesByFingerprint f
    | none, none => pure #[]
  let rows := rows.filter fun cert =>
    (match fingerprint with
      | some f => cert.entry.fingerprint.toLower == f.toLower
      | none => true) &&
    (match hasher with | some h => cert.entry.claim.hasher == h | none => true)
  let rows := ordered rows
  let me := app.config.publicUrl
  match Auth.query req "format" with
  | some "bundle" =>
    -- §3.1: only signed entries federate, so the bundle form drops the rest.
    let entries := (rows.filter (·.federates)).map (entryJson · me)
    let revocations ← app.store.revocationsFor hash hasher fingerprint
    json Response.ok (Json.mkObj [
      ("protocol", Json.str Trust.Federation.protocolVersion),
      ("origin", Json.str me),
      ("entries", Json.arr entries),
      ("revocations", Json.arr (revocations.map toJson)),
      ("complete", Json.bool true)])
  | _ =>
    let byLogin ← avatars app
    json Response.ok (Json.mkObj [
      ("certificates", Json.arr (rows.map fun cert =>
        certificateJson cert me ((byLogin.get? cert.hints.issuer).getD ""))),
      ("truncated", Json.bool false),
      ("askedPeers", toJson (0 : Nat))])

/-! ## §4.1 Export -/

/--
The last cursor a page may honestly hand back.

Entries and withdrawals are two logs read with one cursor, and the cursor a
receiver stores has to be a position *both* of them have been read up to.  If
either page truncated, the resume point is the earlier of the two ends and
everything past it is dropped from this response — otherwise a receiver
resuming from a certificate's cursor would step over the revocations that lie
between, and a withdrawal that is skipped is the one message it is worst to
skip.
-/
private def jointBound (certs : Page StoredCertificate) (revs : Page Trust.SignedRevocation) :
    Option Cursor :=
  let endOf {α : Type} (page : Page α) : Option Cursor :=
    if page.truncated then (page.rows.back?).map (·.cursor) else none
  match endOf certs, endOf revs with
  | some a, some b => some (if b.after a then a else b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

/--
`GET /api/certificates/export?since=&limit=`.

Public and unauthenticated: everything it returns is signed, and a signature
carries the same weight to a stranger as to a friend.  `attested` rows are not
here — §3.1 forbids exporting them, and this is the place that would leak them.

`complete` is set from whether either log was actually cut short, because a
receiver that mistakes truncation for exhaustion silently stops syncing.
-/
private def exportBundle (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  let maximum := app.config.policy.maxEntries
  let asked := (Auth.query req "limit").bind (·.toNat?) |>.getD maximum
  let limit := if asked == 0 then maximum else min asked maximum
  let since := (Auth.query req "since").getD ""
  let certPage ← app.store.certificatesSince since limit
  let revPage ← app.store.revocationsSince since limit
  let bound := jointBound certPage revPage
  let within {α : Type} (row : Row α) : Bool :=
    match bound with | some c => !(row.cursor.after c) | none => true
  let me := app.config.publicUrl
  -- Tombstones are on the page and are dropped here: §4 has no shape for "this
  -- row went away", so a deletion travels no further than this node.
  let entries := ((certPage.rows.filter within).filterMap (·.value)).filter (·.federates)
  let revocations := (revPage.rows.filter within).filterMap (·.value)
  let cursor :=
    match bound with
    | some c => c.encode
    | none =>
      match (certPage.rows.back?).map (·.cursor), (revPage.rows.back?).map (·.cursor) with
      | some a, some b => (if b.after a then b else a).encode
      | some a, none => a.encode
      | none, some b => b.encode
      -- Nothing new: hand back what was asked for, so an idle peer does not
      -- walk back to the beginning of the log.
      | none, none => since
  json Response.ok (Json.mkObj [
    ("protocol", Json.str Trust.Federation.protocolVersion),
    ("origin", Json.str me),
    ("entries", Json.arr (entries.map (entryJson · me))),
    ("revocations", Json.arr (revocations.map toJson)),
    ("cursor", Json.str cursor),
    ("complete", Json.bool bound.isNone)])

/-! ## §6 Revocation -/

/--
`POST /api/revocations`.

Accepted from anyone, signed in or not, because **the signature is the
authorisation**: only the key that made an assertion can withdraw it, and
demanding an account as well would mean somebody who has lost access to theirs
can never take a certificate back.

The check is `Trust.Federation.acceptRevocation`, which is §6.1 and §6.2 rule 1
together — including that the withdrawal is signed by the key it names, without
which anyone could withdraw anyone's assertion by signing a message about it.
-/
private def revoke (app : App) (req : Request Body.Stream) : ContextAsync (Response Body.Any) := do
  let .ok body ← bodyJson app req | return ← badRequest "expected a JSON body"
  let .ok revocationJson := body.getObjVal? "revocation" |
    return ← badRequest "revocation must be an object"
  let .ok revocation := fromJson? (α := Trust.Revocation) revocationJson |
    return ← badRequest "revocation must be an object with fingerprint, hash, hasher and revoked"
  let signature := (body.getObjValAs? String "signature").toOption.getD ""
  let offered := (body.getObjValAs? String "key").toOption.getD ""
  let key ←
    if !offered.isEmpty then pure offered
    else do
      -- A key this node already has is as good as one sent along with the
      -- withdrawal: §6.2 rule 1 is about which key signed, not where it came from.
      let stored ← app.store.keyByFingerprint revocation.fingerprint
      pure ((stored.map (·.armored)).getD "")
  if key.isEmpty then
    return ← badRequest "no key here with that fingerprint; send it with the revocation"
  let signed : Trust.SignedRevocation :=
    { revocation, signature, key, fingerprint := revocation.fingerprint }
  match ← Trust.Federation.acceptRevocation signed app.verifier with
  | .error rejection => badRequest rejection.describe
  | .ok _ =>
    let _ ← app.store.putRevocation signed
    json Response.ok (Json.mkObj [
      ("ok", Json.bool true), ("canonical", Json.str revocation.canonical)])

/-! ## §4.2 Import -/

/-- The hints an arriving entry travelled with, by the triple that identifies it. -/
private def hintsInBundle (body : Json) : Std.HashMap String Hints := Id.run do
  let .ok entries := body.getObjVal? "entries" | return {}
  let .ok rows := entries.getArr? | return {}
  let mut out : Std.HashMap String Hints := {}
  for row in rows do
    let str (j : Json) (k : String) : String := (j.getObjValAs? String k).toOption.getD ""
    let .ok claim := row.getObjVal? "claim" | continue
    let key := certificateKey (str row "fingerprint") (str claim "hash") (str claim "hasher")
    let hints : Hints :=
      match row.getObjVal? "hints" with
      | .ok h => { issuer := str h "issuer", keyVerifiedVia := str h "keyVerifiedVia",
                   origin := str h "origin" }
      | .error _ => {}
    out := out.insert key hints
  return out

/--
`POST /api/import`.

§3.4 for every entry and §6 for every revocation, through
`Trust.Federation.checkBundle`, then what survives is stored.  Rejections are
counted and *described* rather than swallowed: a node that silently drops
entries is indistinguishable from one that is broken.

Authenticated, because the worst an open import endpoint can do is fill a disk —
and not authenticated in local mode, where the only person who can reach the
node is the person whose database it is (§9).
-/
private def importBundle (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) := do
  if !(app.config.localMode || isAdmin app req) then
    return ← fail Response.forbidden "this endpoint is the operator’s"
  let .ok body ← bodyJson app req | return ← badRequest "expected a JSON body"
  let .ok bundle := fromJson? (α := Trust.Bundle) body | return ← badRequest "unreadable bundle"
  -- §2: a receiver that does not recognise the version must not proceed.
  if bundle.protocol != Trust.Federation.protocolVersion then
    return ← badRequest
      s!"this node speaks {Trust.Federation.protocolVersion}, and that bundle says `{bundle.protocol}`"
  let (report, entries, revocations) ← Trust.Federation.checkBundle bundle app.verifier
  let origin := if bundle.origin.isEmpty then "pushed" else bundle.origin
  let hints := hintsInBundle body
  let now ← nowMs
  for entry in entries do
    let claim := entry.claim
    let key := certificateKey entry.fingerprint claim.hash claim.hasher
    let hint := (hints.get? key).getD {}
    let _ ← app.store.putCertificate {
      entry
      hints := {
        issuer := hint.issuer
        -- A key that arrived on the wire is tied to nothing this node checked,
        -- whatever the sender says it checked (§4.4).
        keyVerifiedVia := "remote"
        origin := if hint.origin.isEmpty then bundle.origin else hint.origin }
      fromPeer := origin
      fetchedMs := now }
  for revocation in revocations do
    let _ ← app.store.putRevocation revocation
  json Response.ok (Json.mkObj [
    ("accepted", toJson report.accepted),
    ("rejected", toJson report.rejected),
    ("revocations", toJson report.revocations),
    ("reasons", Json.arr (report.reasons.map Json.str))])

/-! ## Trust lists -/

private def followJson (identity : Option Identity) (login : String) : Json :=
  Json.mkObj [
    ("login", Json.str login),
    ("avatarUrl", Json.str ((identity.map (·.avatarUrl)).getD ""))]

/-- `GET /api/trust-list`, and `GET /api/trust` under the shorter name. -/
private def trustList (app : App) (req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Auth.withIdentity app req fun identity => do
    let follows ← app.store.listFollows identity.login
    let mut people := #[]
    for follow in follows.qsort (·.target < ·.target) do
      if follow.kind != "login" then continue
      people := people.push (followJson (← app.store.getIdentity follow.target) follow.target)
    let keys := (follows.filter (·.kind == "key")).qsort (·.target < ·.target) |>.map fun follow =>
      Json.mkObj [("fingerprint", Json.str follow.target), ("label", Json.str follow.label)]
    json Response.ok (Json.mkObj [
      ("trusted", Json.arr people), ("keys", Json.arr keys)])

/-- `POST /api/trust-list/:login`. -/
private def followLogin (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  Auth.withIdentity app req fun identity => do
    let login := Auth.pathTail req "/api/trust-list/"
    match ← app.store.getIdentity login with
    | none => fail Response.notFound "nobody here by that name has published anything"
    | some _ =>
      app.store.putFollow { truster := identity.login, target := login, kind := "login" }
      json Response.ok (Json.mkObj [("ok", Json.bool true)])

/-- `DELETE /api/trust-list/:login`. -/
private def unfollowLogin (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  Auth.withIdentity app req fun identity => do
    app.store.deleteFollow identity.login "login" (Auth.pathTail req "/api/trust-list/")
    json Response.ok (Json.mkObj [("ok", Json.bool true)])

/--
`POST /api/trust-keys/:fingerprint`.

The portable half of a trust list: a login only means something on the server
that issued it, and a certificate that arrives from three hops away carries a
fingerprint and nothing else you could have checked.
-/
private def followKey (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  Auth.withIdentity app req fun identity => do
    let fingerprint := (Auth.pathTail req "/api/trust-keys/").toLower
    let hex := fingerprint.all fun c => ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')
    if !(hex && fingerprint.length ≥ 16 && fingerprint.length ≤ 64) then
      return ← badRequest "that is not a fingerprint"
    let label := match ← bodyJson app req with
      | .ok body => ((body.getObjValAs? String "label").toOption.getD "").take 100 |>.toString
      | .error _ => ""
    app.store.putFollow
      { truster := identity.login, target := fingerprint, kind := "key", label }
    json Response.ok (Json.mkObj [("ok", Json.bool true)])

/-- `DELETE /api/trust-keys/:fingerprint`. -/
private def unfollowKey (app : App) (req : Request Body.Stream) :
    ContextAsync (Response Body.Any) :=
  Auth.withIdentity app req fun identity => do
    app.store.deleteFollow identity.login "key"
      (Auth.pathTail req "/api/trust-keys/").toLower
    json Response.ok (Json.mkObj [("ok", Json.bool true)])

/--
`GET /api/trusted?hasher=`.

Every hash your trust list vouches for, as one flat set — what the frontend
actually needs, since it already knows how to turn "these declarations are
trusted" into graph semantics.

Non-transitive by construction: the joins go one hop, so trusting somebody never
silently enrols the people *they* trust.  Federation widens who you can hear
from, not whom you trust.

Withdrawals apply here too.  A trusted set that kept counting a certificate its
issuer had taken back would be the one place the withdrawal did not arrive — and
the place it matters most, since this is what decides where a dependency tree
stops.
-/
private def trusted (app : App) (req : Request Body.Stream) : ContextAsync (Response Body.Any) :=
  Auth.withIdentity app req fun identity => do
    let hasher := Auth.query req "hasher"
    let follows ← app.store.listFollows identity.login
    let logins := (follows.filter (·.kind == "login")).map (·.target)
    let keys := (follows.filter (·.kind == "key")).map (·.target.toLower)
    let mut seen : Std.HashMap String Unit := {}
    let mut out := #[]
    for cert in ← app.store.liveCertificates do
      let claim := cert.entry.claim
      if let some h := hasher then
        if claim.hasher != h then continue
      let byKey := keys.contains cert.entry.fingerprint.toLower && !cert.entry.fingerprint.isEmpty
      -- A login is only meaningful for a row this node issued: an `issuer` hint
      -- on a federated entry is the sender's word and §4.4 forbids acting on it.
      let byLogin := cert.isLocal && logins.contains cert.hints.issuer
      if !(byKey || byLogin) then continue
      if ← app.store.isRevoked cert.entry.fingerprint claim.hash claim.hasher claim.asserted then
        continue
      let key := certificateKey cert.entry.fingerprint claim.hash claim.hasher
      if seen.contains key then continue
      seen := seen.insert key ()
      out := out.push (Json.mkObj [
        ("hash", Json.str claim.hash), ("hasher", Json.str claim.hasher),
        ("fingerprint", Json.str cert.entry.fingerprint),
        ("asserted", Json.str claim.asserted)])
    json Response.ok (Json.mkObj [("hashes", Json.arr out)])

/--
Everything about certificates, in the order the router tries them.

`/api/certificates/export` comes before the prefix routes under
`/api/certificates/` on purpose: the first route that claims a request wins, and
a `GET` of the export must not be answered by anything else.
-/
def certificateRoutes : Array Route := #[
  { method := .get, path := "/api/health", run := health },
  { method := .get, path := "/api/federation", run := federation },
  { method := .get, path := "/api/certificates/export", run := exportBundle },
  { method := .get, path := "/api/certificates", run := certificates },
  { method := .post, path := "/api/certificates", run := publish },
  { method := .delete, path := "/api/certificates/", run := withdraw },
  { method := .post, path := "/api/revocations", run := revoke },
  { method := .post, path := "/api/import", run := importBundle },
  { method := .get, path := "/api/trust-list", run := trustList },
  -- The name the task list uses; the frontend says `/api/trust-list`, and one
  -- of them being an alias is cheaper than either client being wrong.
  { method := .get, path := "/api/trust", run := trustList },
  { method := .post, path := "/api/trust-list/", run := followLogin },
  { method := .delete, path := "/api/trust-list/", run := unfollowLogin },
  { method := .post, path := "/api/trust-keys/", run := followKey },
  { method := .delete, path := "/api/trust-keys/", run := unfollowKey },
  { method := .get, path := "/api/trusted", run := trusted }]

end Routes

end TrustServer
