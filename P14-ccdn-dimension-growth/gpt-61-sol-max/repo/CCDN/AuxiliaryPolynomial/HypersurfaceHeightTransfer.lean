/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.RankNumerics

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor
import CCDN.Analysis.HeightRatio

/-!
CCDN Lemma 4.2.3: replace the full coefficient height by any lower height
in the bad-prime contribution, uniformly in the degree.

Uniform comparison of logarithmic coefficient-height ratios.
-/

public section
namespace CCDN

/-- Replace an upper height by any lower height with a dimension-only loss. -/
private theorem logarithmic_height_ratio_le {H Y q c r : ℝ}
    (hY : 1 ≤ Y) (hYH : Y ≤ H) (hq : 0 < q) (hc : 0 < c)
    (hr : 1 ≤ r) (hrqc : 1 ≤ r * (q * c)) :
    (Real.log H + c) / H ^ q ≤ r * ((Real.log Y + c) / Y ^ q) := by
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  have hu := mul_nonneg hq.le (Real.log_nonneg hY)
  have huv :=
    mul_le_mul_of_nonneg_left (Real.log_le_log hY0 hYH) hq.le
  have hh := weighted_exp_ratio_le hu huv (mul_pos hq hc) hr hrqc
  rw [Real.rpow_def_of_pos hH0, Real.rpow_def_of_pos hY0]
  apply (mul_le_mul_iff_right₀ hq).mp
  rw [mul_comm (Real.log H) q, mul_comm (Real.log Y) q]
  convert hh using 1 <;> ring

end CCDN

namespace CCDN

variable {r d : ℕ} (hr : 0 < r) (hd : 0 < d)


include hr hd in
/-- The coefficient-weighted ratio has loss at most r in dimension r. -/
theorem hypersurface_logarithmic_height_transfer 
    {H Y : ℝ} (hY : 1 ≤ Y) (hYH : Y ≤ H) :
    (Real.log H + ↑d ^ 2) / H ^ (1 / (↑r * d * dimensionRoot r d)) ≤
      r * ((Real.log Y + ↑d ^ 2) / Y ^ (1 / (↑r * d * dimensionRoot r d))) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hroot : 0 < dimensionRoot r d := by positivity
  apply logarithmic_height_ratio_le hY hYH (by positivity) (by positivity) hr1
  have he : ↑r * (1 / (↑r * d * dimensionRoot r d) * ↑d ^ 2) =
      ↑d / dimensionRoot r d := by field_simp
  rw [he]
  exact (one_le_div hroot).mpr ((by
                                  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
                                  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
                                  have he := (div_le_one (by linarith)).mpr hr1
                                  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd1 he))

/-- The exponent bookkeeping `d ^ (4 - 1 / (n + 1)) = d ^ (2 - 1 / (n + 1)) * d ^ 2` used by the
affine minimum and height-transfer estimates. -/
lemma rpow_four_sub_eq_mul_sq {d : ℝ} (hd : 0 < d) (n : ℕ) :
    d ^ (4 - 1 / (n + 1 : ℝ)) = d ^ (2 - 1 / (n + 1 : ℝ)) * d ^ 2 := by
  rw [← Real.rpow_natCast d 2, ← Real.rpow_add hd]
  congr 1
  norm_num
  ring

/-- CCDN Lemma 4.2.3 with an explicit dimension constant. The coefficient
height is the maximum, and the bad-prime factor is the defined factor. -/
theorem hypersurface_badPrime_height_transfer {n d : ℕ}
    (f : CCDN.IntegerPolynomial (n + 3))
    (hdegree : f.totalDegree = d) (hd : 0 < d)
    {Y : ℝ} (hY : 1 ≤ Y) (hYH : Y ≤ (integerCoefficientHeight f : ℝ)) :
    ↑d ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor f /
        (integerCoefficientHeight f : ℝ) ^ (heightExponent n d) ≤
      ((n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3)) *
        ↑d ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log Y + ↑d ^ 2) /
          Y ^ (heightExponent n d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  let H := (integerCoefficientHeight f : ℝ)
  have hH : 1 ≤ H := by linarith
  let q := heightExponent n d
  let C := Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3)
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
  have hbad := by
    simpa only [hdegree] using hypersurfaceBadPrimeFactor_le_height f H hH
      (coefficient_abs_le_integerCoefficientHeight f)
  have hratio := by
    simpa only [dimensionRoot, Nat.cast_add, Nat.cast_one] using
      hypersurface_logarithmic_height_transfer (r := n + 1) (by omega) hd hY hYH
  have hpowers :=
    rpow_four_sub_eq_mul_sq hd0 n
  have hstep : ↑d ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor f / H ^ q ≤
      C * ↑d ^ (2 - 1 / (n + 1 : ℝ)) * ((Real.log H + ↑d ^ 2) / H ^ q) := by
    calc
      _ ≤ ↑d ^ (4 - 1 / (n + 1 : ℝ)) * (C * (1 + Real.log H / ↑d ^ 2)) / H ^ q :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbad (by positivity)) (by positivity)
      _ = _ := by rw [hpowers]; field_simp; ring
  have hlast := mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ C * ↑d ^ (2 - 1 / (n + 1 : ℝ)) by positivity)
  apply hstep.trans
  convert hlast using 1
  dsimp only [C]
  ring

end CCDN
