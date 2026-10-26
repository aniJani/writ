import Writ.Api

namespace WritWasm

open Writ

@[export writ_lean_check]
def check (a : String) : String := Api.check a

@[export writ_lean_digest]
def digest (a : String) : String := Api.digest a

@[export writ_lean_canonical]
def canonical (a : String) : String := Api.canonical a

/-- An empty digest means "use the digest of the policy", as in the WASM ABI. -/
@[export writ_lean_initial]
def initial (a b : String) : String := Api.initial a (if b.isEmpty then none else some b)

@[export writ_lean_step]
def step (a b c : String) : String := Api.step a b c

@[export writ_lean_replay]
def replay (a : String) : String := Api.replay a

/-- `b` is `"1"` to set the tombstone and `"0"` to clear it. -/
@[export writ_lean_tombstone]
def tombstone (a b : String) : String :=
  match b with
  | "1" => Api.tombstone a true
  | "0" => Api.tombstone a false
  | _ => (Json.obj #[("error", .str "the tombstone flag must be \"1\" or \"0\"")]).compact

/-- `c` is the time in milliseconds as decimal digits. -/
@[export writ_lean_inspect]
def inspect (a b c : String) : String :=
  match Api.parseTime c with
  | .ok time => Api.inspect a b time
  | .error (input, msg) => Api.fail input msg

@[export writ_lean_profile]
def profile (a : String) : String := Api.profile a

@[export writ_lean_version]
def version (_ : Unit) : String :=
  s!"writ {cliVersion} (kernel {kernelVersion}, trace {traceSchema}, state {stateSchema})"

end WritWasm
