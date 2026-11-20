/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairLowerLifting
public import VaughtConjecture.Knight.CanonicalRecursiveBountiful

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveInitialized

open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev Ready (n : ℕ) (hn : n + 2 ≤ A.card) : Prop :=
  (GradeCutBoundary.rows (CanonicalRecursiveContract.stageCarrier sem n hn) (n + 2)
    (CanonicalRecursiveSemantics.stage sem hp n hn).rows).IsBountiful

variable (hold : CanonicalCoatomBountiful.OldLifts sem)

variable {L R : Finset ι} (hL : L ∈ D.plan) (hR : R ∈ D.plan)

variable (hLA : L ≠ A) (hRA : R ≠ A) (hO : L ∩ R ∈ D.plan)

variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)

include hold hL hR hLA hRA hO hcover in
private theorem base_bountiful (hA : 2 ≤ A.card) (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ 2 →
      ∃ d : Cell D, D.cell d = (C, i)) :
    (GradeCutBoundary.rows (CanonicalPairLocalSections.carrier sem hA) 2 (CanonicalPairLocalSections.semantics sem hA hp)).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (GradeCutBoundary.grade_bound (CanonicalPairLocalSections.carrier sem hA) 2) (by decide)
  intro C B i hC hB hi hCB
  apply (GradeCutLifting.lift_iff (CanonicalPairLocalSections.semantics sem hA hp) 2 _ hi).mpr
  exact CanonicalPairLowerLifting.lower_lift sem hp hA
    hold hL hR hLA hRA hLc hRc hO hcover hcomplete hC hB ⟨hCB, le_rfl⟩ hi

include hold hL hR hLA hRA hO hcover in
theorem ready (n : ℕ) (hA : n + 2 ≤ A.card)
    (hLc : n + 2 ≤ L.card) (hRc : n + 2 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ n + 2 →
      ∃ d : Cell D, D.cell d = (C, i)) : Ready sem hp n hA := by
  induction n with
  | zero => exact base_bountiful sem hp hold hL hR hLA hRA hO hcover hA hLc hRc hcomplete
  | succ n ih =>
    exact CanonicalRecursiveBountiful.bountiful sem n hA hp
      (ih (Nat.le_of_succ_le hA) (Nat.le_of_succ_le hLc) (Nat.le_of_succ_le hRc)
        (fun C hC hCA i hi hic hin => hcomplete C hC hCA i hi hic (by omega)))
      hold hL hR hLA hRA hLc hRc hO hcover
      (fun C hC hCA hic => hcomplete C hC hCA (n + 3) (by omega) hic le_rfl)

include hold hL hR hLA hRA hO hcover in
/-- Actual lower-domain lifting at every constructed grade, including equal
indices, arbitrary lawful prescriptions, literal top, and all auxiliary caps.
No serving controller, alignment, completion, or initial bountifulness is supplied. -/
theorem lift (n : ℕ) (hA : n + 3 ≤ A.card)
    (hLc : n + 3 ≤ L.card) (hRc : n + 3 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ n + 3 →
      ∃ d : Cell D, D.cell d = (C, i))
    {I J : Finset ι × ℕ} (hI : I ∈ Plan.gradedPlan D.plan)
    (hJ : J ∈ Plan.gradedPlan D.plan) (h : GradedLe I J) (hJk : J.2 ≤ n + 3) :
    CappedLift (CanonicalRecursiveSemantics.rows sem hp n hA) h := by
  apply (GradeCutLifting.lift_iff (CanonicalRecursiveSemantics.rows sem hp n hA)
    (n + 3) h hJk).mp
  apply lift_of_bountiful (ready sem hp hold hL hR hLA hRA hO hcover
    (n + 1) hA hLc hRc hcomplete)
  · change I ∈ Plan.gradedPlan (CanonicalRecursiveContract.carrier sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]; exact hI
  · change J ∈ Plan.gradedPlan (CanonicalRecursiveContract.carrier sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]; exact hJ

end

end VaughtConjecture.Knight.CanonicalRecursiveInitialized
