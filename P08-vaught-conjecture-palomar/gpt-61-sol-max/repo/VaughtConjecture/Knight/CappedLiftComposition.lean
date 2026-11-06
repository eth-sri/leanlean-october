/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.CoatomBoundaryExtension
import VaughtConjecture.Knight.FullScopeBountiful

/-! # Composition of literal original-cap lifting clauses

The intermediate ambient is an actual restriction of the target-local input.
No whole ambient extension or output bountifulness is assumed.
-/

namespace VaughtConjecture.Knight.CoatomBoundaryExtension
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  {sem : Semantics D} 

/-- Raise only the target grade after a proved same-grade scope lift. -/
theorem CappedLift.raise_target {B C} {i j}
    {h : B ⊆ C} (hl : CappedLift sem (show GradedLe (B, i) (C, i) from ⟨h, le_rfl⟩))
    (hij : i ≤ j) : CappedLift sem (show GradedLe (B, i) (C, j) from ⟨h, hij⟩) :=
  hl.comp 
    (bountiful_same_scope sem  (i := i) (j := j) ⟨Finset.Subset.refl _, hij⟩)

