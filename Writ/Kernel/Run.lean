import Writ.Kernel.Step

namespace Writ

def run (p : Policy) (s : State) : List Event → State × List Verdict
  | [] => (s, [])
  | e :: es =>
    let (s', v) := step p s e
    let (s'', vs) := run p s' es
    (s'', v :: vs)

end Writ
