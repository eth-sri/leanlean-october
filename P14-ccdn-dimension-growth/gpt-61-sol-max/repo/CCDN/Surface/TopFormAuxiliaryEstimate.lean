/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.RankNumerics

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.AuxiliaryPolynomial.AffineHypersurfaceAuxiliary
import CCDN.AuxiliaryPolynomial.HypersurfaceHeightTransfer

/-! Uniform coefficient absorption and affine-box estimates for the
auxiliary theorem with an irreducible leading homogeneous form. -/

public section
namespace CCDN
open MvPolynomial

/-- For a nonzero integer polynomial `f` of degree `d > 0` with coefficient height `H` and for
`r > 0`, the bad-prime factor of `f` divided by `H^(1/(r d d^(1/r)))` is bounded by a constant
depending only on `r` and the number of variables. -/
theorem hypersurface_badPrime_fractional_height_bound {m r d : ℕ}
    (f : CCDN.IntegerPolynomial (m + 1)) (hf : f ≠ 0)
    (hdegree : f.totalDegree = d) (hr : 0 < r) (hd : 0 < d) :
    hypersurfaceBadPrimeFactor f /
        (integerCoefficientHeight f : ℝ) ^ (1 / (↑r * d * dimensionRoot r d)) ≤
      r * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (m + 1) := by
  let H := (integerCoefficientHeight f : ℝ)
  let q := 1 / (↑r * d * dimensionRoot r d)
  let K := Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (m + 1)
  have hH : 1 ≤ H := by dsimp only [H]; exact_mod_cast integerCoefficientHeight_pos f hf
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
  have hb := by
    simpa only [hdegree] using hypersurfaceBadPrimeFactor_le_height f H hH
      (coefficient_abs_le_integerCoefficientHeight f)
  have hratio := by
    simpa only [Real.log_one, zero_add, Real.one_rpow, div_one] using
      hypersurface_logarithmic_height_transfer hr hd  le_rfl hH
  calc
    _ ≤ (K / ↑d ^ 2) * ((Real.log H + ↑d ^ 2) / H ^ q) := by
      have hh := div_le_div_of_nonneg_right hb (show 0 ≤ H ^ q by positivity)
      convert hh using 1
      field_simp
      ring
    _ ≤ (K / ↑d ^ 2) * (r * ↑d ^ 2) :=
      mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by dsimp only [K]; field_simp

variable (n : ℕ) {d : ℕ} (hd : 0 < d)

include hd in
private lemma affine_auxiliary_lower_terms_bound 
    {B : ℝ} (hB : 1 ≤ B) :
    ↑d ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B + ↑d ^ (4 - 1 / (n + 1 : ℝ)) ≤
      2 * ↑d ^ (4 - 1 / (n + 1 : ℝ)) * B ^ (1 / degreeRoot n d) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hn1 : (1 : ℝ) ≤ n + 1 := by simp_all
  have hexp : 1 ≤ 4 - 1 / (n + 1 : ℝ) := by
    have hh := (div_le_one (by positivity : (0 : ℝ) < n + 1)).mpr hn1
    linarith
  have hdD := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hd1 hexp
  let Q := B ^ (1 / degreeRoot n d)
  have hQ : 1 ≤ Q := Real.one_le_rpow hB (by positivity)
  have hlog : Real.log B ≤ degreeRoot n d * Q := by
    have hh := Real.log_le_rpow_div (by linarith : 0 ≤ B)
      (by positivity : 0 < 1 / degreeRoot n d)
    simpa only [Q, one_div, div_inv_eq_mul, mul_comm] using hh
  have hpowers : ↑d ^ (1 - 1 / (n + 1 : ℝ)) *
      degreeRoot n d = d := by
    rw [← Real.rpow_add hd0, sub_add_cancel, Real.rpow_one]
  have hfirst := by
    calc
      _ ≤ ↑d ^ (1 - 1 / (n + 1 : ℝ)) *
          (degreeRoot n d * Q) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = d * Q := by rw [← mul_assoc, hpowers]
      _ ≤ _ := mul_le_mul_of_nonneg_right hdD (by positivity)
  have hsecond : ↑d ^ (4 - 1 / (n + 1 : ℝ)) ≤
      ↑d ^ (4 - 1 / (n + 1 : ℝ)) * Q :=
    le_mul_of_one_le_right (by positivity) hQ
  change _ ≤ 2 * ↑d ^ (4 - 1 / (n + 1 : ℝ)) * Q
  linarith

include hd in
/-- A uniform bound on the coefficient-weighted bad-prime factor removes
both the coefficient dependence and the logarithmic box term. -/
theorem affineAuxiliaryDegreeExpression_le_of_badPrime_ratio  {B L b K : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L)
    (hratio : b / L ^ (heightExponent n d) ≤ K) :
    affineAuxiliaryDegreeExpression n d B L b ≤
      (K + 2) * ↑d ^ (4 - 1 / (n + 1 : ℝ)) *
        B ^ (1 / degreeRoot n d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  let q := heightExponent n d
  let Q := B ^ (1 / degreeRoot n d)
  have hpowers :=
    (rpow_four_sub_eq_mul_sq hd0 n).symm
  have hmain :
      ↑d ^ (2 - 1 / (n + 1 : ℝ)) *
        min (Real.log L + d * Real.log B + ↑d ^ 2) (↑d ^ 2 * b) * Q / L ^ q ≤
      K * ↑d ^ (4 - 1 / (n + 1 : ℝ)) * Q := by
    calc
      _ ≤ ↑d ^ (2 - 1 / (n + 1 : ℝ)) * (↑d ^ 2 * b) * Q / L ^ q := by
        gcongr
        exact min_le_right _ _
      _ = (↑d ^ (2 - 1 / (n + 1 : ℝ)) * ↑d ^ 2) * Q * (b / L ^ q) := by ring
      _ ≤ (↑d ^ (2 - 1 / (n + 1 : ℝ)) * ↑d ^ 2) * Q * K :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = _ := by rw [hpowers]; ring
  have hlower := affine_auxiliary_lower_terms_bound n hd hB
  unfold affineAuxiliaryDegreeExpression
  dsimp only [q, Q] at hmain
  nlinarith only [hmain, hlower]

end CCDN
