/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases

/-! The numerical comparison for CCDN Proposition 5. A square grid with
floor((d-1)/2)+1 points per side at radius floor((d+1)/4) already gives
the stated degree-squared lower bound, with the exact constant 1/5. -/

namespace CCDN

lemma degree_square_le_five_fourths_power (d : ℕ) :
    ((d : ℝ) + 1) ^ 2 ≤ 16 * (5 / 4 : ℝ) ^ d := by
  induction d with
  | zero => norm_num
  | succ d ih =>
    by_cases hd : d < 8
    · interval_cases d <;> norm_num
    · have hdR : (8 : ℝ) ≤ d := mod_cast (show 8 ≤ d by omega)
      have hs : (d + 2) ^ 2 ≤ (5 / 4 : ℝ) * (d + 1) ^ 2 := by
        nlinarith
      calc
        (((d + 1 : ℕ) : ℝ) + 1) ^ 2 = ((d : ℝ) + 2) ^ 2 := by grind
        _ ≤ (5 / 4 : ℝ) * (d + 1) ^ 2 := hs
        _ ≤ (5 / 4 : ℝ) * (16 * (5 / 4 : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by grind

section
variable {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 0 ≤ B) (hsize : 4 * B ≤ (d : ℝ) + 1)
include hd hB hsize

/-- The radius used in the grid construction has B^(2/d) at most 5/4. -/
theorem grid_radius_rpow_le_five_fourths
    :
    B ^ (2 / (d : ℝ)) ≤ 5 / 4 := by
  have hh := degree_square_le_five_fourths_power d
  have hs :=
    pow_le_pow_left₀ (by positivity) hsize 2
  have hpow : B ^ 2 ≤ (5 / 4 : ℝ) ^ d := by nlinarith
  have hdR : (0 : ℝ) < d := mod_cast hd
  apply (Real.rpow_le_rpow_iff (Real.rpow_nonneg hB _) (by norm_num) hdR).mp
  rw [← Real.rpow_mul hB]
  have he : (2 / (d : ℝ)) * d = 2 := by field_simp
  rw [he]
  simpa using hpow

/-- The grid cardinality dominates the exact lower bound in Proposition 5. -/
theorem grid_square_card_lower_bound
    :
    ((d : ℝ) ^ 2 / 5) * B ^ (2 / (d : ℝ)) ≤
      (((d - 1) / 2 + 1 : ℕ) : ℝ) ^ 2 := by
  let s := (d - 1) / 2 + 1
  have hdsR : (d : ℝ) ≤ 2 * (s : ℝ) := mod_cast (by grind)
  have hs : (d : ℝ) ^ 2 / 4 ≤ (s : ℝ) ^ 2 := by
    nlinarith
  calc
    _ ≤ ((d : ℝ) ^ 2 / 5) * (5 / 4) :=
      mul_le_mul_of_nonneg_left (grid_radius_rpow_le_five_fourths hd hB hsize) (by positivity)
    _ = (d : ℝ) ^ 2 / 4 := by ring
    _ ≤ _ := hs

end

