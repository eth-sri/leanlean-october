/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveBountiful

/-! # Initialized bountiful grade recursion on the actual canonical rows

Seed lifting is proved directly on its complete persistent inventory. The
banked lower-pair theorem supplies restoration; no equivalence of catalogues
is used to import three-grade bountifulness. The established successor then
iterates from this constructed base, within the explicit old-coatom bounds.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveInitialized
open Transform Value ExtOrd CoatomBoundaryExtension AmalgamationPlan
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : D.AvoidsScope A)
variable (hold : CoatomBoundaryExtension.OldLifts sem)
variable {L R : Finset ι} (hL : L ∈ D.plan) (hR : R ∈ D.plan)
variable (hLA : L ≠ A) (hRA : R ≠ A) (hO : L ∩ R ∈ D.plan)
variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)

abbrev CutBountiful (n : ℕ) (hA : n ≤ A.card) :=
  (GradeCutBoundary.rows (CanonicalRecursiveContract.carrier sem n hA) n
    (CanonicalRecursiveSemantics.rows sem hp n hA)).IsBountiful

include hold hL hR hLA hRA hO hcover in
/-- Grade-zero cuts have no cells. Every positive cut uses the same successor. -/
theorem ready n (hA : n ≤ A.card) (hLc : n ≤ L.card) (hRc : n ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ n →
      ∃ d, D.cell d = (C,i)) : CutBountiful sem hp n hA := by
  induction n with
  | zero =>
    intro I J _ _ h _
    let E := CanonicalRecursiveContract.carrier sem 0 hA
    let Z := GradeCutBoundary.scheme E 0
    letI : IsEmpty (Z.below I) := ⟨fun d => (Nat.not_lt_of_ge
      (GradeCutBoundary.grade_bound E 0 d.1)) (Z.grade_pos d.1)⟩
    exact lift_empty h
  | succ n ih =>
    exact CanonicalRecursiveBountiful.bountiful sem n hA hp
      (ih (by omega) (by omega) (by omega) (fun C h hCA i hi hic hin =>
        hcomplete C h hCA i hi hic (by omega))) hold hL hR hLA hRA hLc hRc hO hcover
      (fun C h hCA hc => hcomplete C h hCA _ (Nat.succ_pos _) hc le_rfl)

include hold hL hR hLA hRA hO hcover in
/-- Actual lower-domain lifting at every constructed grade, including equal
indices, arbitrary lawful prescriptions, literal top, and all auxiliary caps.
No serving controller, alignment, completion, or initial bountifulness is supplied. -/
theorem lift n (hA : n ≤ A.card)
    (hLc : n ≤ L.card) (hRc : n ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ n →
      ∃ d, D.cell d = (C, i))
    {I J} (hI : I ∈ Plan.gradedPlan D.plan)
    (hJ : J ∈ Plan.gradedPlan D.plan) (h : GradedLe I J) (hJk : J.2 ≤ n) :
    CappedLift (CanonicalRecursiveSemantics.rows sem hp n hA) h := by
  apply (GradeCutLifting.lift_iff (CanonicalRecursiveSemantics.rows sem hp n hA)
    n h hJk).mp
  apply lift_of_bountiful (ready sem hp hold hL hR hLA hRA hO hcover
    n hA hLc hRc hcomplete)
  · change I ∈ Plan.gradedPlan (CanonicalRecursiveContract.carrier sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]; exact hI
  · change J ∈ Plan.gradedPlan (CanonicalRecursiveContract.carrier sem n hA).plan
    rw [CanonicalRecursiveBoundaryTransport.plan_eq]; exact hJ

end
end VaughtConjecture.Knight.CanonicalRecursiveInitialized
