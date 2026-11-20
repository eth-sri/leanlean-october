/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.AmalgamatedBoundary

/-! # Literal semantics on a uniformly ordered proper boundary

The two inherited tables are glued on their exact occurrence overlap.
No display is recoded and no faithful transformations are composed.
Only equality of the shared source rows is required for row installation.
-/

@[expose] public section

namespace VaughtConjecture.Knight.AmalgamatedBoundaryRows

open AmalgamationPlan AmalgamatedBoundaryPlan AmalgamatedBoundary
open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι]

open Classical in
/-- Extend a semantic row by bottom outside its actual lower domain. -/
noncomputable def total {B : Finset ι} {D : CellScheme B} (sem : Semantics D)
    (c d : Cell D) : ExtOrd :=
  if h : GradedLe (D.cell d) (D.cell c) then sem.E c ⟨d, h⟩ else ⊥

theorem total_below {B : Finset ι} {D : CellScheme B} sem
    c (d : D.RowDomain c) : total sem c d.1 = sem.E c d := by
  rw [total, dite_eq_left d.2]
  exact congrArg (sem.E c) (Subtype.ext rfl)

theorem total_outside {B : Finset ι} {D : CellScheme B} sem
    c d (h : ¬ GradedLe (D.cell d) (D.cell c)) : total sem c d = ⊥ := by
  simp only [total, dite_eq_right h]

section Push
variable {B C : Finset ι} {D : CellScheme B} {K : CellScheme C}
variable (f : Cell D → Cell K) (hf : Function.Injective f)
variable (hi : ∀ d, K.cell (f d) = D.cell d) (sem : Semantics D)

noncomputable def pushRow (c : Cell D) : K.Labelling :=
  Function.extend f (total sem c) (fun _ => ⊥)

include hf in
theorem pushRow_at c d : pushRow f sem c (f d) = total sem c d :=
  hf.extend_apply _ _ _

include hf hi in
theorem pushRow_outside c z
    (hz : ¬ GradedLe (K.cell z) (D.cell c)) : pushRow f sem c z = ⊥ := by
  classical
  by_cases h : ∃ d, f d = z
  · obtain ⟨d, rfl⟩ := h
    rw [pushRow_at f hf]
    apply total_outside
    simpa only [hi] using hz
  · exact Function.extend_apply' _ _ _ h

end Push

end VaughtConjecture.Knight.AmalgamatedBoundaryRows
