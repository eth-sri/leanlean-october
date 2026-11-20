/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section
namespace CCDN
open Finset

/-- Sum a geometric majorant shell by shell. -/
theorem geometric_shell_sum {ι : Type*} (S : Finset ι) (h w : ι → ℝ) {r M : ℝ}
    (hr : 1 < r) (hM : 0 ≤ M) (hh : ∀ i ∈ S, 1 < h i)
    (bound : ∀ (k : ℕ) (T : Finset ι), T ⊆ S → (∀ i ∈ T, r^k < h i ∧ h i ≤ r^(k+1)) →
      ∑ i ∈ T, w i ≤ M*(1/2:ℝ)^k) : ∑ i ∈ S, w i ≤ 2*M := by
  classical
  have band (i) (hi : i ∈ S) : ∃ k : ℕ, r^k < h i ∧ h i ≤ r^(k+1) := by
    have hex : ∃ k : ℕ, h i ≤ r^k := (pow_unbounded_of_one_lt (h i) hr).imp fun _ h => h.le
    generalize he : Nat.find hex = n
    cases n with
    | zero => have := Nat.find_spec hex; simp [he] at this; linarith [hh i hi]
    | succ k => exact ⟨k,lt_of_not_ge (Nat.find_min hex (by omega : k < Nat.find hex)),he ▸ Nat.find_spec hex⟩
  choose! b hb using band
  let N := S.sup b + 1
  have hN (i) (hi : i ∈ S) : b i ∈ range N := mem_range.mpr (Nat.lt_succ_of_le (le_sup hi))
  rw [← sum_fiberwise_of_maps_to hN]
  calc _ ≤ ∑ k ∈ range N, M*(1/2:ℝ)^k := sum_le_sum fun k _ => bound k _ (filter_subset ..) (by grind)
       _ ≤ _ := by rw [← mul_sum,mul_comm 2]; gcongr; exact sum_geometric_two_le _

end CCDN
