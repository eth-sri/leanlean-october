/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport

open Transform Value ExtOrd CanonicalRecursiveContract

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D)

theorem plan_eq (m : ℕ) (hm : m ≤ A.card) :
    (CanonicalRecursiveInventory.scheme sem m hm).plan = D.plan := by
  induction m with
  | zero => rfl
  | succ m ih => tauto

open CanonicalRecursiveInventory (proper_below patch)

abbrev properEquiv (n : ℕ) (hA : n + 2 ≤ A.card) (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1) :
    D.below J ≃ (stageCarrier sem n hA).below J :=
  CellScheme.belowEquivOfIndex (stageBoundary sem n hA) (stageBoundary sem n hA).injective
    (CanonicalRecursiveInventory.boundary_cell sem (n + 2) hA) (proper_below sem (n + 2) hA J hJ)

variable (hp : ∀ d : Cell D, D.scope d ≠ A)

theorem pullback_respects (n : ℕ) (hA : n + 2 ≤ A.card) (J : Finset ι × ℕ) (hJ : ¬ A ⊆ J.1)
    {p : (stageCarrier sem n hA).below J → ExtOrd}
    (hpr : RespectsSemanticsBelow (CanonicalRecursiveSemantics.stage sem hp n hA).rows J p) :
    RespectsSemanticsBelow sem J (p ∘ properEquiv sem n hA J hJ) :=
  (iff_comp_symm (properEquiv sem n hA J hJ).symm
    ((patch sem hp (n + 2) hA).respects_iff (CanonicalRecursiveSemantics.stage sem hp n hA).row J
      (proper_below sem (n + 2) hA J hJ)) p).mp hpr

abbrev row (n : ℕ) (hA : n + 3 ≤ A.card) := (CanonicalRecursiveSemantics.state sem hp n hA).row

/-- Proper targets retain all original rows and all original lifting clauses. -/
theorem proper_lift (n : ℕ) (hA : n + 3 ≤ A.card) {I J : Finset ι × ℕ}
    (h : GradedLe I J) (hJ : ¬ A ⊆ J.1) (hl : CoatomBoundaryExtension.CappedLift sem h) :
    CoatomBoundaryExtension.CappedLift (CanonicalRecursiveSemantics.rows sem hp n hA) h :=
  (patch sem hp (n + 3) hA).lift (row sem hp n hA) h (proper_below sem (n + 3) hA J hJ) hl

end

end VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport
