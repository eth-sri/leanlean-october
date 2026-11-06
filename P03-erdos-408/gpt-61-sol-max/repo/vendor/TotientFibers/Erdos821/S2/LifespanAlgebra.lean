module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring.RingNF

/-! Polynomial identities underlying the one-prime lifespan expansion. -/

@[expose] public section

section
open scoped BigOperators

namespace Erdos821.S2

lemma prefix_ghost_ordered {ι R : Type*} [LinearOrder ι] [CommRing R]
    (s : Finset ι) (f : ι → R) :
    (∏ i ∈ s, (1 - f i)) =
      1 - ∑ j ∈ s, f j * ∏ i ∈ s.filter (fun i => j < i), (1 - f i) := by
  classical
  exact Finset.prod_one_sub_ordered (ι := OrderDual ι) s f

end Erdos821.S2
