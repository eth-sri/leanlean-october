/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Explicit exponent margins for the small-degree surface argument.
The estimates hold uniformly for every degree at least five and absorb any
fixed power of the logarithm; geometric covering hypotheses are separate. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- For every natural number `d ≥ 5`, `1 / √d ≤ 9 / 20`. -/
theorem surface_inverse_sqrt_le_nine_twentieths {d : ℕ} (hd : 5 ≤ d) :
    1 / Real.sqrt (d : ℝ) ≤ (9 / 20 : ℝ) := by
  have hs : (20 / 9 : ℝ) ≤ Real.sqrt (d : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith [show (5 : ℝ) ≤ d by exact_mod_cast hd])
  simpa [one_div] using inv_anti₀ (by norm_num) hs

/-- A fixed logarithmic power costs at most any prescribed positive power,
with an explicit constant independent of the box radius. -/
theorem logarithm_add_one_pow_le_rpow (k : ℕ) {ε B : ℝ}
    (hε : 0 < ε) (hB : 1 ≤ B) :
    (Real.log B + 1) ^ k ≤
      ((k.factorial : ℝ) / ε ^ k * Real.exp ε) * B ^ ε := by
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hh := Real.pow_div_factorial_le_exp (ε * (Real.log B + 1)) (by positivity) k
  rw [show Real.exp (ε * (Real.log B + 1)) = Real.exp ε * B ^ ε by
    rw [Real.rpow_def_of_pos (by linarith), ← Real.exp_add]; ring_nf, mul_pow] at hh
  have hm := (div_le_iff₀ (mod_cast Nat.factorial_pos k)).mp hh
  exact ((le_div_iff₀' (pow_pos hε k)).mpr hm).trans_eq (by ring)

/-- Retained nonlinear curves with square-root box count and any fixed
polylogarithmic loss contribute O(B) once their number has the
B^(1/sqrt(d)) scale, for every d>=5. -/
theorem surface_nonlinear_polylog_weight {d : ℕ} (hd : 5 ≤ d) (k : ℕ)
    {B : ℝ} (hB : 1 ≤ B) :
    B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2) * (Real.log B + 1) ^ k ≤
      ((k.factorial : ℝ) / (1 / 20 : ℝ) ^ k * Real.exp (1 / 20)) * B := by
  let C : ℝ := (k.factorial : ℝ) / (1 / 20 : ℝ) ^ k * Real.exp (1 / 20)
  have he : 1 / Real.sqrt (d : ℝ) + 1 / 2 + 1 / 20 ≤ (1 : ℝ) := by
    linarith [surface_inverse_sqrt_le_nine_twentieths hd]
  calc B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2) * (Real.log B + 1) ^ k
    _ ≤ B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2) * (C * B ^ (1 / 20 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (logarithm_add_one_pow_le_rpow k (by norm_num) hB) (by positivity)
    _ = C * B ^ (1 / Real.sqrt (d : ℝ) + 1 / 2 + 1 / 20) := by
      rw [Real.rpow_add (by linarith) (1 / Real.sqrt (d : ℝ) + 1 / 2) (1 / 20)]; ring
    _ ≤ C * B := mul_le_mul_of_nonneg_left
      (by simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hB he) (by positivity)

end
end CCDN
