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
  have hdR : (5 : ℝ) ≤ d := by exact_mod_cast hd
  have hs : (20 / 9 : ℝ) ≤ Real.sqrt (d : ℝ) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 20 / 9) hs
  linarith

/-- The constant for absorbing a logarithmic power into a positive power. -/
abbrev logarithmicBoxConstant (k : ℕ) (ε : ℝ) : ℝ :=
  (k.factorial : ℝ) / ε ^ k * Real.exp ε

/-- A fixed logarithmic power costs at most any prescribed positive power,
with an explicit constant independent of the box radius. -/
theorem logarithm_add_one_pow_le_rpow (k : ℕ) {ε B : ℝ}
    (hε : 0 < ε) (hB : 1 ≤ B) :
    (Real.log B + 1) ^ k ≤
      logarithmicBoxConstant k ε * B ^ ε := by
  have hB0 : 0 < B := by linarith
  have hlog : 0 ≤ Real.log B := Real.log_nonneg hB
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hh := Real.pow_div_factorial_le_exp (ε * (Real.log B + 1))
    (show 0 ≤ ε * (Real.log B + 1) by positivity) k
  have he : Real.exp (ε * (Real.log B + 1)) = Real.exp ε * B ^ ε := by
    rw [Real.rpow_def_of_pos hB0, ← Real.exp_add]
    congr 1
    ring
  rw [he, mul_pow] at hh
  have hm := (div_le_iff₀ hfac).mp hh
  calc
    _ ≤ (Real.exp ε * B ^ ε * (k.factorial : ℝ)) / ε ^ k := by
      apply (le_div_iff₀ (pow_pos hε k)).mpr
      linarith
    _ = _ := by unfold logarithmicBoxConstant; ring

/-- A positive exponent margin absorbs a logarithmic factor in a linear bound. -/
theorem box_polylog_weight (k : ℕ) {t ε B : ℝ}
    (hε : 0 < ε) (hB : 1 ≤ B) (ht : t + ε ≤ 1) :
    B ^ t * (Real.log B + 1) ^ k ≤ logarithmicBoxConstant k ε * B := by
  calc
    _ ≤ B ^ t * (logarithmicBoxConstant k ε * B ^ ε) :=
      mul_le_mul_of_nonneg_left (logarithm_add_one_pow_le_rpow k hε hB) (by positivity)
    _ = logarithmicBoxConstant k ε * B ^ (t + ε) := by
      rw [Real.rpow_add (by positivity)]
      ring
    _ ≤ _ := by
      gcongr
      simpa using Real.rpow_le_rpow_of_exponent_le hB ht

end
end CCDN
