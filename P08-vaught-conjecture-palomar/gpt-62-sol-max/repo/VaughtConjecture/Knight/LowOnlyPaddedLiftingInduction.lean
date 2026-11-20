/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedFibre
public import VaughtConjecture.Knight.LowOnlyPaddedIteration
public import VaughtConjecture.Knight.EffectiveGradeLifting

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedLiftingInduction

open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse

open LowOnlyPaddedContract Padded.StepRows LowOnlyOrderedLadder

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : I.RootMatches F.root)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)

open LowOnlyPaddedIteration AmalgamationPlan CoatomBoundaryExtension

include hcover

local notation "t₀" => (A.card - 2)
local notation "L" => build I F hroot hA hB hC t₀ (by omega)

/-- The original face lifts at all cutoffs give bountifulness at the full height. -/
theorem full_bountiful : (L).rows.IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_same_grade
  intro S U i hS hU hSU
  rw [build_plan I F hroot hA hB hC t₀ (by omega)] at hS hU
  have hu := Plan.mem_gradedPlan.mp hU
  have hcard : U.card ≤ A.card := Finset.card_le_card (I.isPlan.subset_of_mem hu.1)
  have hui : i ≤ U.card := hu.2.2
  have hi : i ≤ t₀ + 2 := by omega
  exact I.same_grade_of_faces ((L).face I.leftFace hB.not_ge) ((L).face I.rightFace hC.not_ge)
    hB.subset hC.subset hcover
    (fun h => (LowOnlyPaddedFibre.donorNative I F hroot hA hB hC).capped_clause
      I.consistent hB t₀ (by omega) (Plan.mem_gradedPlan.mp h).2.1 hi)
    (fun h => (LowOnlyPaddedFibre.privateNative I F hroot hA hB hC).capped_clause
      I.consistent hC t₀ (by omega) (Plan.mem_gradedPlan.mp h).2.1 hi)
    hS hU hSU

theorem full_complete : (L).carrier.IsComplete := by
  rintro ⟨S, j⟩ hJ
  rw [build_plan I F hroot hA hB hC t₀ (by omega)] at hJ
  obtain ⟨hS, hj, hcard⟩ := Plan.mem_gradedPlan.mp hJ
  by_cases h : S = A
  · subst S
    change j ≤ A.card at hcard
    exact (L).full_occupied (by omega) j hj (by omega)
  · obtain ⟨d, hd⟩ := (I.occupied_iff hJ).mpr (hcover S hS h)
    exact ⟨(L).original d, ((L).original_index d).trans hd⟩

end

end VaughtConjecture.Knight.LowOnlyPaddedLiftingInduction
