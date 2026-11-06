/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases

/-! The numerical comparison for CCDN Proposition 5. A square grid with
floor((d-1)/2)+1 points per side at radius floor((d+1)/4) already gives
the stated degree-squared lower bound, with the exact constant 1/5. -/

@[expose] public section
namespace CCDN

/-- The grid cardinality dominates the exact lower bound in Proposition 5. -/
theorem grid_square_card_lower_bound {d : ℕ} (hd : 0 < d)
    {B : ℝ} (hB : 0 ≤ B) (hsize : 4 * B ≤ (d : ℝ) + 1) :
    ((d : ℝ) ^ 2 / 5) * B ^ (2 / (d : ℝ)) ≤
      (((d - 1) / 2 + 1 : ℕ) : ℝ) ^ 2 := by
  /- The radius used in the grid construction has B^(2/d) at most 5/4. -/
  have hh (n : ℕ) : ((n : ℝ) + 1) ^ 2 ≤ 16 * (5 / 4 : ℝ) ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      by_cases hn8 : n < 8
      · interval_cases n <;> norm_num
      · have hnR : (8 : ℝ) ≤ n := mod_cast (show 8 ≤ n by omega)
        calc
          (((n + 1 : ℕ) : ℝ) + 1) ^ 2 = ((n : ℝ) + 2) ^ 2 := by push_cast; ring
          _ ≤ (5 / 4 : ℝ) * ((n : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg ((n : ℝ) - 8)]
          _ ≤ (5 / 4 : ℝ) * (16 * (5 / 4 : ℝ) ^ n) := mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = _ := by rw [pow_succ]; ring
  have hhd := hh d
  have hs_pow : (4 * B) ^ 2 ≤ ((d : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hsize 2
  have hpow : B ^ 2 ≤ (5 / 4 : ℝ) ^ d := by nlinarith
  have hdR : (0 : ℝ) < d := mod_cast hd
  have hrpow : B ^ (2 / (d : ℝ)) ≤ 5 / 4 := by
    apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hB _) (by norm_num) hdR).mp
    rw [← Real.rpow_mul hB, show (2 / (d : ℝ)) * d = 2 by field_simp]
    simpa only [Real.rpow_two, Real.rpow_natCast] using hpow
  let s := (d - 1) / 2 + 1
  have hdsR : (d : ℝ) ≤ 2 * (s : ℝ) := mod_cast (show d ≤ 2 * s by dsimp [s]; omega)
  calc
    _ ≤ ((d : ℝ) ^ 2 / 5) * (5 / 4) := mul_le_mul_of_nonneg_left hrpow (by positivity)
    _ = (d : ℝ) ^ 2 / 4 := by ring
    _ ≤ _ := by nlinarith [sq_nonneg ((s : ℝ) - (d : ℝ) / 2)]

/-- For `d > 0`, `⌊(d - 1) / 2⌋ - ⌊(d - 1) / 4⌋ = ⌊(d + 1) / 4⌋`, relating the grid size to the
radius in the numerics for CCDN Proposition 5. -/
lemma grid_lower_bound_radius_identity (d : ℕ) (hd : 0 < d) :
    (d - 1) / 2 - (d - 1) / 4 = (d + 1) / 4 := by omega

/-- For `d ≥ 3`, the grid radius `⌊(d + 1) / 4⌋` is at least `1`. -/
lemma grid_lower_bound_radius_pos {d : ℕ} (hd : 3 ≤ d) :
    1 ≤ (d + 1) / 4 := by omega

/-- The grid radius satisfies `4 ⌊(d + 1) / 4⌋ ≤ d + 1`. -/
lemma grid_lower_bound_radius_size (d : ℕ) :
    4 * (((d + 1) / 4 : ℕ) : ℝ) ≤ (d : ℝ) + 1 := by
  exact_mod_cast (show 4 * ((d + 1) / 4) ≤ d + 1 by omega)

end CCDN
