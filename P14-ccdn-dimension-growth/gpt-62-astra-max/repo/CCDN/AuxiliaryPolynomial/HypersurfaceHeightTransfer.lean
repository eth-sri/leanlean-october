/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Equations
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor

/-!
CCDN Lemma 4.2.3: replace the full coefficient height by any lower height
in the bad-prime contribution, uniformly in the degree.

Uniform comparison of logarithmic coefficient-height ratios.
-/

@[expose] public section
namespace CCDN

private lemma weighted_exp_ratio_le {u v a r : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (ha : 0 < a) (hr : 1 ≤ r) (hra : 1 ≤ r * a) :
    (v + a) / Real.exp v ≤ r * ((u + a) / Real.exp u) := by
  have hru : 1 ≤ r * (u + a) := by nlinarith
  have he := by
    exact Real.add_one_le_exp (v - u)
  have hh : v + a ≤ r * (u + a) * Real.exp (v - u) := by
    nlinarith
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (Real.exp_pos v) (Real.exp_pos u)).mpr
  have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos u).le
  grind [mul_assoc, Real.exp_add, sub_add_cancel]

/-- Replace an upper height by any lower height with a dimension-only loss. -/
private theorem logarithmic_height_ratio_le {H Y q c r : ℝ}
    (hY : 1 ≤ Y) (hYH : Y ≤ H) (hq : 0 < q) (hc : 0 < c)
    (hr : 1 ≤ r) (hrqc : 1 ≤ r * (q * c)) :
    (Real.log H + c) / H ^ q ≤ r * ((Real.log Y + c) / Y ^ q) := by
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  have hh := weighted_exp_ratio_le (mul_nonneg hq.le (Real.log_nonneg hY)) (mul_le_mul_of_nonneg_left (Real.log_le_log hY0 hYH) hq.le) (mul_pos hq hc) hr hrqc
  rw [Real.rpow_def_of_pos hH0, Real.rpow_def_of_pos hY0]
  apply (mul_le_mul_iff_right₀ hq).mp
  grind

end CCDN

namespace CCDN
noncomputable section

variable {m r d : ℕ} (hr : 0 < r) (hd : 0 < d)

include hr hd in
private lemma dimension_root_le_degree :
    (d : ℝ) ^ (1 / (r : ℝ)) ≤ d := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  simpa using Real.rpow_le_rpow_of_exponent_le hd1 ((div_le_one (by linarith)).mpr hr1)

include hr hd in
/-- The coefficient-weighted ratio has loss at most r in dimension r. -/
theorem hypersurface_logarithmic_height_transfer
    {H Y : ℝ} (hY : 1 ≤ Y) (hYH : Y ≤ H) :
    (Real.log H + (d : ℝ) ^ 2) / H ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      r * ((Real.log Y + (d : ℝ) ^ 2) / Y ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ))))) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hroot : (0 : ℝ) < (d : ℝ) ^ (1 / (r : ℝ)) := by positivity
  apply logarithmic_height_ratio_le hY hYH (by positivity) (by positivity) hr1
  have he : (r : ℝ) * (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ))) * (d : ℝ) ^ 2) =
      (d : ℝ) / (d : ℝ) ^ (1 / (r : ℝ)) := by field_simp
  rw [he]
  exact (one_le_div hroot).mpr (dimension_root_le_degree hr hd)

section

variable (m : ℕ)

abbrev badHeightCost := Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant m

lemma badHeightCost_nonneg : 0 ≤ badHeightCost m :=
  by grind [mul_nonneg, Real.exp_pos, hypersurfaceHeightConstant_one_le]

end

include hr hd in
/-- Transfer any logarithmically bounded charge to a lower height scale. -/
lemma normalized_bad_factor {b c H Y : ℝ}
    (hc : 0 ≤ c) (hY : 1 ≤ Y) (hYH : Y ≤ H) (hb : b ≤ c * (1 + Real.log H / (d : ℝ)^2)) :
    let q := 1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))
    b / H^q ≤ (r*c) * (1 + Real.log Y / (d : ℝ)^2) / Y^q := by
  intro q
  calc
    _ ≤ c * (1 + Real.log H / d^2) / H^q := div_le_div_of_nonneg_right hb (Real.rpow_nonneg (by linarith) _)
    _ = c / d^2 * ((Real.log H + d^2) / H^q) := by field_simp; ring
    _ ≤ c / d^2 * (r * ((Real.log Y + d^2) / Y^q)) :=
      mul_le_mul_of_nonneg_left (hypersurface_logarithmic_height_transfer hr hd hY hYH) (by positivity)
    _ = _ := by field_simp; ring

/-- For a nonzero integer polynomial `f` of degree `d > 0` with coefficient height `H` and for
`r > 0`, the bad-prime factor of `f` divided by `H^(1/(r d d^(1/r)))` is bounded by a constant
depending only on `r` and the number of variables. -/
theorem hypersurface_badPrime_fractional_height_bound
    (f : IntegerPolynomial (m + 1)) (hf : f ≠ 0)
    (hdegree : f.totalDegree = d) (hr : 0 < r) (hd : 0 < d) :
    hypersurfaceBadPrimeFactor f /
        (integerCoefficientHeight f : ℝ) ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      r * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (m + 1) := by
  have hH : (1 : ℝ) ≤ integerCoefficientHeight f := by exact_mod_cast integerCoefficientHeight_pos f hf
  have hh := normalized_bad_factor hr hd (badHeightCost_nonneg (m+1)) (le_refl 1) hH
    (hdegree ▸ hypersurfaceBadPrimeFactor_le_height f _ hH (coefficient_abs_le_integerCoefficientHeight f))
  simpa [mul_assoc] using hh

end
end CCDN
