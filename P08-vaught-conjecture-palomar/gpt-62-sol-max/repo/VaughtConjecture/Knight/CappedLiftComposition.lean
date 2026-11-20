/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoatomBoundaryExtension
public import VaughtConjecture.Knight.FullScopeBountiful

@[expose] public section

namespace VaughtConjecture.Knight.CoatomBoundaryExtension

open Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

/-- Raise only the target grade after a proved same-grade scope lift. -/
theorem CappedLift.raise_target {B C : Finset ι} {i j : ℕ}
    {h : B ⊆ C} (hl : CappedLift sem (show GradedLe (B, i) (C, i) from ⟨h, le_rfl⟩))
    (hij : i ≤ j) : CappedLift sem (show GradedLe (B, i) (C, j) from ⟨h, hij⟩) :=
  hl.comp (hJK := by trivial)
    (bountiful_same_scope sem (B := C) (i := i) (j := j) ⟨Finset.Subset.refl _, hij⟩)

end VaughtConjecture.Knight.CoatomBoundaryExtension
