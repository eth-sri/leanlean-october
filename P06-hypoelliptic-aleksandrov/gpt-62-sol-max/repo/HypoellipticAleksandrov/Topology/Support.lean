module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Support

/-!
# Continuity from localized topological support

This module records a support-local continuity gluing lemma for real-valued
functions on an arbitrary topological space.
-/

@[expose] public section

namespace HypoellipticAleksandrov

/-- The product of two functions continuous on an open set is globally
continuous when the topological support of the first lies in that set. -/
theorem continuous_mul_of_tsupport_subset
    {X : Type*} [TopologicalSpace X] {U : Set X} {b q : X → ℝ}
    (hU : IsOpen U) (hb : ContinuousOn b U) (hbsupp : tsupport b ⊆ U)
    (hq : ContinuousOn q U) :
    Continuous (fun x => b x * q x) := by
  exact ContinuousOn.continuous_of_tsupport_subset (ContinuousOn.mul hb hq) hU (LE.le.trans tsupport_mul_subset_left hbsupp)

end HypoellipticAleksandrov
