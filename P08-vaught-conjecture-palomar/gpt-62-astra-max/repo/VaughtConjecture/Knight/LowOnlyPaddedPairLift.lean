/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedTowerLifting
public import VaughtConjecture.Knight.LowOnlyPaddedStepSupply
public import VaughtConjecture.Knight.LowOnlyPaddedStepPrivateRepair
public import VaughtConjecture.Knight.LowOnlyPaddedStepDonorRepair
public import VaughtConjecture.Knight.LowOnlyDonorOrderedLift

/-! # Lifting through the installed LowOnly faces -/

@[expose] public section
namespace VaughtConjecture.Knight.LowOnlyPaddedPairLift
open LowOnlyPaddedContract LowOnlyPaddedIteration CoatomBoundaryExtension AmalgamationPlan
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
  {m n K : ℕ} {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  (frame : I.LowFrame F)

theorem private_clause (t : ℕ) (ht : t+1 ≤ A.card) {j : ℕ}
    (hj : 1 ≤ j) (hface : j ≤ n) (hlt : j ≤ t+1) :
    CappedLift (before frame t ht).rows (GradedLe.atGrade frame.rightProper.subset j) := by
  apply PaddedTower.buildLift (system frame) frame.rightProper.subset ?_ ?_ t ht hj hface hlt
  · apply PlacedFace.lift (S := I.right) ((PaddedTower.seed (system frame)).face I.rightFace frame.rightProper.not_ge)
      le_rfl (min_le_left _ _) frame.rightProper.subset
    exact fun hp hq hv ha => LowOnlyOrderedLadder.private_lift I F frame.attachment frame.positive
      frame.leftProper frame.rightProper hp hq hv ha
  · intro k P hk ht hn hl
    apply PlacedFace.successor (S := I.right) ((PaddedTower.successor P hk ht).face I.rightFace frame.rightProper.not_ge)
      le_rfl (min_le_left _ _) frame.rightProper.subset hl
    · exact LowOnlyPaddedStepSupply.private_bottom_supply P hk ht
    · exact LowOnlyPaddedStepPrivateRepair.owner_capped P hk ht

theorem donor_clause (t : ℕ) (ht : t+1 ≤ A.card) {j : ℕ}
    (hj : 1 ≤ j) (hface : j ≤ n) (hlt : j ≤ t+1) :
    CappedLift (before frame t ht).rows (GradedLe.atGrade frame.leftProper.subset j) := by
  apply PaddedTower.buildLift (system frame) frame.leftProper.subset ?_ ?_ t ht hj hface hlt
  · apply PlacedFace.lift (S := I.left) ((PaddedTower.seed (system frame)).face I.leftFace frame.leftProper.not_ge)
      le_rfl (min_le_left _ _) frame.leftProper.subset
    exact fun hp hq hv ha => LowOnlyOrderedLadder.donor_lift I F frame.attachment frame.positive
      frame.leftProper frame.rightProper hp hq hv ha
  · intro k P hk ht hn hl
    apply PlacedFace.successor (S := I.left) ((PaddedTower.successor P hk ht).face I.leftFace frame.leftProper.not_ge)
      le_rfl (min_le_left _ _) frame.leftProper.subset hl
    · exact LowOnlyPaddedStepSupply.donor_bottom_supply P hk ht
    · exact LowOnlyPaddedStepDonorRepair.owner_capped P hk ht

/-- The intended binary coface plan supplies coverage by construction.
This does not assert coverage for a larger plan containing new mixed scopes. -/
theorem cover_two_cofaces (s : AmalgamatedBoundaryPlan.Step A)
    (hR : R = s.plan) (hleft : B = A.erase s.a) (hright : C = A.erase s.b) :
    ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C := by
  intro S hS hs
  rw [hR] at hS
  rcases Finset.mem_union.mp hS with hS | hS
  · rcases Finset.mem_union.mp hS with hl | hr
    · exact Or.inl (hleft ▸ s.left_plan.subset_of_mem hl)
    · exact Or.inr (hright ▸ s.right_plan.subset_of_mem hr)
  · exact False.elim (hs (Finset.mem_singleton.mp hS))

end
end VaughtConjecture.Knight.LowOnlyPaddedPairLift
