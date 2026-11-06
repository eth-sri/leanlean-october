module

public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold

/-- Label a vertex by parity along its right-parent path. Root edges carry
zero, so extra recursion depth does not alter the intended path parity. -/
def diamondPotential {V : Type*} (right : V → V) (rightEdge : V → Bool) :
    ℕ → V → Bool
  | 0, _ => false
  | k + 1, v => rightEdge v ^^ diamondPotential right rightEdge k (right v)

end HordijkSteelThreshold
