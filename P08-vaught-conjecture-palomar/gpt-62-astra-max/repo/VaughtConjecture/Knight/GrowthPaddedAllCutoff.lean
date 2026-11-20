/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedTowerLifting
public import VaughtConjecture.Knight.GrowthPaddedStepSupply
public import VaughtConjecture.Knight.GrowthPaddedStepPrivateRepair
public import VaughtConjecture.Knight.GrowthPaddedStepDonorRepair
public import VaughtConjecture.Knight.GrowthGradeOneLift

/-! # Lifting through the installed Growth faces -/

@[expose] public section
namespace VaughtConjecture.Knight.GrowthPaddedAllCutoff
open GrowthPaddedContract GrowthPaddedIteration CoatomBoundaryExtension AmalgamationPlan
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
  {m n J : ℕ} {I : WholeDonorBoundary.Input A B C R m (n+1) J} {X : I.GrowthData}
  (frame : I.GrowthFrame X)

theorem private_clause (t : ℕ) (ht : t+1 ≤ A.card) {j : ℕ}
    (hj : 1 ≤ j) (hface : j ≤ J) (hlt : j ≤ t+1) :
    CappedLift (before frame t ht).rows (GradedLe.atGrade frame.rightProper.subset j) := by
  apply PaddedTower.buildLift (system frame) frame.rightProper.subset ?_ ?_ t ht hj hface hlt
  · apply PlacedFace.lift (S := I.right) ((PaddedTower.seed (system frame)).face I.rightFace frame.rightProper.not_ge)
      (min_le_left _ _) le_rfl frame.rightProper.subset
    exact fun hp hq hv ha => GrowthOrderedBase.private_lift I X frame.attachment frame.positive
      frame.leftProper frame.rightProper hp hq hv ha
  · intro k P hk ht hn hl
    apply PlacedFace.successor (S := I.right) ((PaddedTower.successor P hk ht).face I.rightFace frame.rightProper.not_ge)
      (min_le_left _ _) le_rfl frame.rightProper.subset hl
    · exact GrowthPaddedStepSupply.private_bottom_supply P hk ht
    · exact GrowthPaddedStepPrivateRepair.owner_capped P hk ht

theorem donor_clause (hsmall : n+1 < X.req.N) (t : ℕ) (ht : t+1 ≤ A.card) {j : ℕ}
    (hj : 1 ≤ j) (hface : j ≤ (n+1)) (hlt : j ≤ t+1) :
    CappedLift (before frame t ht).rows (GradedLe.atGrade frame.leftProper.subset j) := by
  apply PaddedTower.buildLift (system frame) frame.leftProper.subset ?_ ?_ t ht hj hface hlt
  · apply PlacedFace.lift (S := I.left) ((PaddedTower.seed (system frame)).face I.leftFace frame.leftProper.not_ge)
      (min_le_left _ _) le_rfl frame.leftProper.subset
    exact fun hp hq hv ha => GrowthOrderedBase.donor_lift_of_arity I X frame.attachment frame.positive
      frame.leftProper frame.rightProper hsmall hp hq hv ha
  · intro k P hk ht hn hl
    apply PlacedFace.successor (S := I.left) ((PaddedTower.successor P hk ht).face I.leftFace frame.leftProper.not_ge)
      (min_le_left _ _) le_rfl frame.leftProper.subset hl
    · exact GrowthPaddedStepSupply.donor_bottom_supply P hk ht (hn.trans_lt hsmall)
    · exact GrowthPaddedStepDonorRepair.owner_capped P hk ht (hn.trans_lt hsmall)

theorem private_subface (t : ℕ) (ht : t+2 ≤ A.card) {S : Finset ι} {i j : ℕ}
    (hS : (S,i) ∈ Plan.gradedPlan R) (hs : S ⊆ C) (hij : i ≤ j) (hj : j ≤ t+2) :
    CappedLift (build frame t ht).rows (show GradedLe (S,i) (A,j) from ⟨hs.trans frame.rightProper.subset,hij⟩) := by
  let L := build frame t ht
  apply I.liftSubface (L.face I.leftFace frame.leftProper.not_ge) (L.face I.rightFace frame.rightProper.not_ge)
    (I.rightPlan_le I.rightScheme.isPlan.domain_mem) (.inr (le_refl _)) hS hs frame.rightProper.subset hij
  intro bound
  exact private_clause frame (t+1) ht (Plan.mem_gradedPlan.mp hS).2.1 (bound.trans_eq I.card_right) (hij.trans hj)

theorem donor_subface (hsmall : n+1 < X.req.N) (t : ℕ) (ht : t+2 ≤ A.card) {S : Finset ι} {i j : ℕ}
    (hS : (S,i) ∈ Plan.gradedPlan R) (hs : S ⊆ B) (hij : i ≤ j) (hj : j ≤ t+2) :
    CappedLift (build frame t ht).rows (show GradedLe (S,i) (A,j) from ⟨hs.trans frame.leftProper.subset,hij⟩) := by
  let L := build frame t ht
  apply I.liftSubface (L.face I.leftFace frame.leftProper.not_ge) (L.face I.rightFace frame.rightProper.not_ge)
    (I.leftPlan_le I.leftScheme.isPlan.domain_mem) (.inl (le_refl _)) hS hs frame.leftProper.subset hij
  intro bound
  exact donor_clause frame hsmall (t+1) ht (Plan.mem_gradedPlan.mp hS).2.1 (bound.trans_eq I.card_left) (hij.trans hj)

end
end VaughtConjecture.Knight.GrowthPaddedAllCutoff
