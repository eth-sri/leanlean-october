module

public import HypoellipticAleksandrov.Parabolic.Geometry
public import Mathlib.Topology.Separation.Regular

/-!
# Nested compact collars for weak representatives

This module records the topological collar used to localize a relatively
compact open carrier before applying compactly supported weak-jet cutoffs.
-/

 public section

open Set

namespace HypoellipticAleksandrov.Parabolic

/-- A relatively compact open set inside an open carrier admits a second
relatively compact open collar. -/
theorem exists_open_compact_closure_collar
    {d : Nat} {U V : HypoellipticAleksandrov.Parabolic.Region d}
    (hU : IsOpen U) (hV : IsOpen V)
    (hVcompact : IsCompact (closure V)) (hVU : closure V ⊆ U) :
    ∃ W : HypoellipticAleksandrov.Parabolic.Region d,
      IsOpen W ∧ IsCompact (closure W) ∧
      closure V ⊆ W ∧ closure W ⊆ U := by
  obtain ⟨L, hLcompact, hLclosed, hVinterior, hLU⟩ :=
    exists_compact_closed_between hVcompact hU hVU

  have hW  := union_eq_left.mpr (subset_closure.trans hVinterior)
  have hclosure  :=
    closure_minimal interior_subset hLclosed



  exact ⟨_, isOpen_interior.union hV, (by
      rw [hW]
      exact IsCompact.of_isClosed_subset hLcompact isClosed_closure hclosure),
    (by
        rw [hW]
        exact hVinterior), (by
        rw [hW]
        exact hclosure.trans hLU)⟩

end HypoellipticAleksandrov.Parabolic
