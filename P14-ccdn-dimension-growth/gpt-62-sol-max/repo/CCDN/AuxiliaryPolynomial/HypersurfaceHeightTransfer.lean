/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.DegreeBound
public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor

/-!
CCDN Lemma 4.2.3: replace the full coefficient height by any lower height
in the bad-prime contribution, uniformly in the degree.

Uniform comparison of logarithmic coefficient-height ratios.
-/

@[expose] public section
namespace CCDN

noncomputable section

/-- Dividing by a power of the height absorbs the increase in its logarithm. -/
private lemma logarithmic_height_ratio_le {H Y q c r : ℝ} (hY : 1 ≤ Y) (hYH : Y ≤ H)
    (hq : 0 < q) (hc : 0 < c) (hr : 1 ≤ r) (hrqc : 1 ≤ r * c * q) :
    (1 + Real.log H / c) / H ^ q ≤ r * ((1 + Real.log Y / c) / Y ^ q) := by
  have hY0 : 0 < Y := by linarith
  have hH0 := hY0.trans_le hYH
  let z := H ^ q / Y ^ q
  have hz : 1 ≤ z := (one_le_div (by positivity)).mpr (Real.rpow_le_rpow hY0.le hYH hq.le)
  have hlog := Real.log_le_sub_one_of_pos (show 0 < z by linarith)
  change Real.log (H ^ q / Y ^ q) ≤ _ at hlog
  rw [Real.log_div (by positivity) (by positivity), Real.log_rpow hH0, Real.log_rpow hY0] at hlog
  have hcost : Real.log H - Real.log Y ≤ r * c * (z - 1) := by nlinarith
  have hy : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hfin : Real.log H + c ≤ r * (c + Real.log Y) * z := by
    nlinarith [mul_le_mul_of_nonneg_right (one_le_mul_of_one_le_of_one_le hr hz) hy, mul_le_mul_of_nonneg_right hr hc.le]
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  apply (mul_le_mul_iff_right₀ hc).mp
  convert mul_le_mul_of_nonneg_right hfin (show 0 ≤ Y ^ q by positivity) using 1
  all_goals
    try dsimp only [z]
    field_simp
  all_goals exact add_comm _ _

/-- The loss in comparing bad-prime factors to a lower coefficient height. -/
def badPrimeHeightConstant (n m : ℕ) : ℝ :=
  (n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (m + 1)

lemma badPrimeHeightConstant_nonneg (n m : ℕ) : 0 ≤ badPrimeHeightConstant n m := by
  have := (hypersurfaceHeightConstant_one_le (m + 1)).trans' zero_le_one
  unfold badPrimeHeightConstant
  positivity

/-- The weighted bad-prime factor is bounded using any lower bound on the height. -/
theorem hypersurface_badPrime_height_transfer {n m d : ℕ}
    (f : MvPolynomial (Fin (m + 1)) ℤ) (hdegree : f.totalDegree = d) (hd : 0 < d)
    {Y : ℝ} (hY : 1 ≤ Y) (hYH : Y ≤ (integerCoefficientHeight f : ℝ)) :
    hypersurfaceBadPrimeFactor f / (integerCoefficientHeight f : ℝ) ^ heightExponent n d ≤
      badPrimeHeightConstant n m * (1 + Real.log Y / (d : ℝ) ^ 2) / Y ^ heightExponent n d := by
  let H := (integerCoefficientHeight f : ℝ)
  let q := heightExponent n d
  let C := Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (m + 1)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hH := hY.trans hYH
  have hC : 0 ≤ C := by
    have := (hypersurfaceHeightConstant_one_le (m + 1)).trans' zero_le_one
    positivity
  have hbad : hypersurfaceBadPrimeFactor f ≤ C * (1 + Real.log H / (d : ℝ) ^ 2) := by
    simpa only [hdegree] using hypersurfaceBadPrimeFactor_le_height f H hH
      (coefficient_abs_le_integerCoefficientHeight f)
  have hr : (1 : ℝ) ≤ (n : ℝ) + 1 := by simp
  have hroot : degreeRoot n d ≤ d := by
    simpa only [degreeRoot, Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast hd : (1 : ℝ) ≤ d) ((div_le_one (by positivity)).mpr hr)
  have hrqc : 1 ≤ (n + 1 : ℝ) * (d : ℝ) ^ 2 * q := by
    simpa only [q, heightExponent, mul_one_div, one_mul, le_div_iff₀ (by positivity : 0 < (n + 1 : ℝ) * d * degreeRoot n d)] using
      (show (n + 1 : ℝ) * d * degreeRoot n d ≤ (n + 1 : ℝ) * (d : ℝ) ^ 2 by
        rw [pow_two, ← mul_assoc]; gcongr)
  calc
    _ ≤ C * ((1 + Real.log H / (d : ℝ) ^ 2) / H ^ q) := by rw [← mul_div_assoc]; gcongr
    _ ≤ C * ((n + 1 : ℝ) * ((1 + Real.log Y / (d : ℝ) ^ 2) / Y ^ q)) :=
      mul_le_mul_of_nonneg_left (logarithmic_height_ratio_le hY hYH (by positivity) (by positivity) hr hrqc) hC
    _ = _ := by unfold badPrimeHeightConstant; dsimp only [C, q]; ring

end
end CCDN
