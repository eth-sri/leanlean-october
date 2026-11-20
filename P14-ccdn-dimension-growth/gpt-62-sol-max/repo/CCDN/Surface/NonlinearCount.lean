/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Statements

/-! Finite union and weighted finite union bounds for bounded integer points. -/

@[expose] public section
namespace CCDN
noncomputable section

section

variable {n : ℕ} {ι : Type*}
  (s : Finset ι) (X : ι → Set (RatPoint n)) (B : ℝ)
include n ι s X B

/-- The number of integral points of height at most `B` on a finite union of sets is at most
the sum of the numbers of such points on the individual sets. -/
theorem count_biUnion_finset_le :
    count (⋃ i ∈ s, X i) B ≤ ∑ i ∈ s, count (X i) B := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [count, integralPoints]
  | @insert i s hi ih =>
    simpa only [Finset.set_biUnion_insert, Finset.sum_insert hi] using
      (count_union_le (X i) (⋃ j ∈ s, X j) B).trans (Nat.add_le_add_left ih _)

/-- A common weighted bound for the terms of a finite union. -/
theorem count_biUnion_finset_mul_le {K C : ℝ} (hK : 0 ≤ K)
    (h : ∀ i ∈ s, (count (X i) B : ℝ) * K ≤ C) :
    (count (⋃ i ∈ s, X i) B : ℝ) * K ≤ s.card * C := by
  have hs : (count (⋃ i ∈ s, X i) B : ℝ) ≤ ∑ i ∈ s, (count (X i) B : ℝ) := by
    exact_mod_cast count_biUnion_finset_le s X B
  calc
    _ ≤ (∑ i ∈ s, (count (X i) B : ℝ)) * K := mul_le_mul_of_nonneg_right hs hK
    _ = ∑ i ∈ s, (count (X i) B : ℝ) * K := Finset.sum_mul ..
    _ ≤ ∑ _i ∈ s, C := Finset.sum_le_sum h
    _ = _ := by simp

end

end
end CCDN
