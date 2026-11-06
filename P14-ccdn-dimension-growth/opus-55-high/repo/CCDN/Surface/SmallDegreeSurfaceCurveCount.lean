/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Statements
import CCDN.Analysis.SmallDegreeSurfaceNumerics
import CCDN.Curve.AffineCurveCount
import CCDN.Surface.NonlinearCount

/-! Nonlinear initial curves whose degrees are at most logarithmic in the
box radius. The full affine curve theorem and the strict surface exponent
gap give a linear bound in every surface degree at least five. -/

namespace CCDN

theorem curveBound_logarithmic_degree {δ : ℕ} (hδ : 2 ≤ δ)
    {B D : ℝ} (hB : 1 ≤ B) (_hD : 0 ≤ D)
    (hδD : (δ : ℝ) ≤ D * (Real.log B + 1)) :
    curveBound δ B ≤ (δ : ℝ) * D ^ 2 * (D + 1) *
      B ^ (1 / 2 : ℝ) * (Real.log B + 1) ^ 3 := by
  have hB0 := zero_lt_one.trans_le hB
  have hlog := Real.log_nonneg hB
  have hδR : (2 : ℝ) ≤ δ := mod_cast hδ
  have hpow :=
    Real.rpow_le_rpow_of_exponent_le hB
      (one_div_le_one_div_of_le (by norm_num) hδR)
  have hsq :=
    pow_le_pow_left₀ (by positivity) hδD 2
  calc
    _ ≤ (δ * (D * (Real.log B + 1)) ^ 2) *
        B ^ (1 / 2 : ℝ) * ((D + 1) * (Real.log B + 1)) := by
      apply mul_le_mul (mul_le_mul (by
        nlinarith) hpow (by positivity) (by positivity)) (by nlinarith)
      · positivity
      · positivity
    _ = _ := by ring

