# trust-server

A trust certificate node: it stores the certificates published to it, holds the
sessions that authenticate the people publishing them, and federates with other
nodes so that a question one node cannot answer can travel to those that can.
It is deliberately not a trusted party — private keys are never uploaded,
signature checks are a cache rather than the authority, and every certificate
is returned with the canonical bytes that were signed so a client can repeat the
check itself.  Written in Lean.  Part of [chrisflav/trust](https://github.com/chrisflav/trust).
