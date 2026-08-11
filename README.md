# trust-server

A trust certificate node: it stores the certificates published to it, holds the
sessions that authenticate the people publishing them, and federates with other
nodes so that a question one node cannot answer can travel to those that can.
It is deliberately not a trusted party — private keys are never uploaded,
signature checks are a cache rather than the authority, and every certificate
is returned with the canonical bytes that were signed so a client can repeat the
check itself.  Written in Lean.  Part of [chrisflav/trust](https://github.com/chrisflav/trust).

## Building

```
lake build          # the library and the `trust-server` executable
lake exe tests      # the test suite; non-zero exit on any failure
```

The toolchain is `leanprover/lean4:v4.32.0`, pinned in `lean-toolchain`.  It is
not a free choice: certificate hashes are computed by a specific revision of
`semantic_hash`, and moving the toolchain moves that revision, which would
silently change what every stored hash means.  `TrustServer/Store.lean` says
more about what that rules out.

## Running

```
TRUST_LOCAL=1 TRUST_STORE_DIR=./store lake exe trust-server
```

`--check` reports what is missing from the configuration and exits; `--dir` and
`--port` override `TRUST_STORE_DIR` and `PORT`.  `TrustServer/Config.lean` is
the whole configuration surface, and it is the only place the environment is
read.

## What is here

* `TrustServer/Store.lean` — the store: a directory of append-only JSONL logs,
  indexed in memory, with §3.5's replacement rule and §6.2's suppression rule
  decided in one place.
* `TrustServer/Config.lean` — the environment, resolved once into a value, with
  the limits of §8 of [`FEDERATION.md`](https://github.com/chrisflav/trust/blob/master/FEDERATION.md).
* `TrustServer.lean` — the server skeleton: `/api/health` and nothing else yet.
