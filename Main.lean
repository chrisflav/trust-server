import Cli
import TrustServer

/-!
# The command line

Argument parsing, the environment, and starting the thing.  Everything it starts
is in `TrustServer.lean`, so that the tests can start the same server without
importing an executable's `main`.
-/

open Cli
open Std Std.Async
open TrustServer


private def runServer (p : Parsed) : IO UInt32 := do
  let fromEnv ← ServerConfig.load
  -- The flags win over the environment, because someone who typed one meant it.
  let config := { fromEnv with
    storeDir := (p.flag? "dir" |>.map (·.as! String)).getD fromEnv.storeDir
    port := (p.flag? "port" |>.map (·.as! Nat)).getD fromEnv.port
    localMode := p.hasFlag "local" || fromEnv.localMode }
  let problems := config.problems
  if p.hasFlag "check" then
    if problems.isEmpty then
      IO.println "configuration is complete"
      return 0
    for problem in problems do IO.eprintln s!"error: {problem}"
    return 1
  if !problems.isEmpty then
    for problem in problems do IO.eprintln s!"error: {problem}"
    return 1
  start config
  return 0

private def serverCmd : Cmd := `[Cli|
  "trust-server" VIA runServer; ["0.1.0"]
  "A trust certificate node: an append-only store, and the HTTP surface over it."

  FLAGS:
    dir : String;   "The directory the append-only logs live in (TRUST_STORE_DIR)."
    port : Nat;     "The port to listen on; 0 picks a free one (PORT)."
    check;          "Report configuration problems and exit."
]

def main (args : List String) : IO UInt32 :=
  serverCmd.validate args
