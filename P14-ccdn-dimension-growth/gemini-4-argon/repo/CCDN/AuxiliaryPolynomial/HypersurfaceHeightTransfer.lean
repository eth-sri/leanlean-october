/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.HypersurfaceBadPrimeFactor

/-!
CCDN Lemma 4.2.3: replace the full coefficient height by any lower height
in the bad-prime contribution, uniformly in the degree.

Uniform comparison of logarithmic coefficient-height ratios.
-/

@[expose] public section
namespace CCDN
noncomputable section

/-- The coefficient-weighted ratio has loss at most r in dimension r. -/
theorem hypersurface_logarithmic_height_transfer {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {H Y : ℝ} (hY : 1 ≤ Y) (hYH : Y ≤ H) :
    (Real.log H + (d : ℝ) ^ 2) / H ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) ≤
      r * ((Real.log Y + (d : ℝ) ^ 2) / Y ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ))))) := by
  have hr1 : (1 : ℝ) ≤ r := mod_cast hr
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  let q := 1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))
  let c := (d : ℝ) ^ 2
  let a := q * c
  have hq : 0 < q := by dsimp [q]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have ha : 0 < a := mul_pos hq hc
  let u := q * Real.log Y
  let v := q * Real.log H
  have hu : 0 ≤ u := mul_nonneg hq.le (Real.log_nonneg hY)
  have huv : u ≤ v := mul_le_mul_of_nonneg_left (Real.log_le_log hY0 hYH) hq.le
  have hroot : (d : ℝ) ^ (1 / (r : ℝ)) ≤ d := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hd1 ((div_le_one (by linarith)).mpr hr1)
  have hra : 1 ≤ (r : ℝ) * a := by
    have he : (r : ℝ) * a = (d : ℝ) / (d : ℝ) ^ (1 / (r : ℝ)) := by dsimp [a, q, c]; field_simp
    rw [he]
    exact (one_le_div (by positivity)).mpr hroot
  have hru : 1 ≤ (r : ℝ) * (u + a) := by nlinarith
  have he : 1 + (v - u) ≤ Real.exp (v - u) := by
    simpa only [add_comm] using Real.add_one_le_exp (v - u)
  have hh : v + a ≤ (r : ℝ) * (u + a) * Real.exp (v - u) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr1) (show 0 ≤ u + a by linarith),
      mul_nonneg (sub_nonneg.mpr hru) (sub_nonneg.mpr huv),
      mul_le_mul_of_nonneg_left he (show 0 ≤ (r : ℝ) * (u + a) by positivity)]
  have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos u).le
  rw [mul_assoc, ← Real.exp_add, sub_add_cancel] at hh'
  have hdiv : (v + a) / Real.exp v ≤ (r : ℝ) * ((u + a) / Real.exp u) := by
    rw [← mul_div_assoc]
    exact (div_le_div_iff₀ (Real.exp_pos v) (Real.exp_pos u)).mpr hh'
  change (Real.log H + c) / H ^ q ≤ (r : ℝ) * ((Real.log Y + c) / Y ^ q)
  rw [Real.rpow_def_of_pos hH0, Real.rpow_def_of_pos hY0]
  apply (mul_le_mul_iff_right₀ hq).mp
  rw [mul_comm (Real.log H) q, mul_comm (Real.log Y) q]
  convert hdiv using 1 <;> dsimp [u, v, a] <;> ring

/-- The exponent bookkeeping `d ^ (4 - 1 / (n + 1)) = d ^ (2 - 1 / (n + 1)) * d ^ 2` used by the
affine minimum and height-transfer estimates. -/
lemma rpow_four_sub_eq_mul_sq {d : ℝ} (hd : 0 < d) (n : ℕ) :
    d ^ (4 - 1 / (n + 1 : ℝ)) = d ^ (2 - 1 / (n + 1 : ℝ)) * d ^ 2 := by
  rw [← Real.rpow_natCast d 2, ← Real.rpow_add hd]; congr 1; ring

/-- CCDN Lemma 4.2.3 with an explicit dimension constant. The coefficient
height is the maximum, and the bad-prime factor is the defined factor. -/
theorem hypersurface_badPrime_height_transfer {n d : ℕ}
    (f : MvPolynomial (Fin (n + 3)) ℤ) (hf : f ≠ 0)
    (hdegree : f.totalDegree = d) (hd : 0 < d)
    {Y : ℝ} (hY : 1 ≤ Y) (hYH : Y ≤ (integerCoefficientHeight f : ℝ)) :
    (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor f /
        (integerCoefficientHeight f : ℝ) ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) ≤
      ((n + 1 : ℝ) * Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3)) *
        (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * (Real.log Y + (d : ℝ) ^ 2) /
          Y ^ (1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))) := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  let H := (integerCoefficientHeight f : ℝ)
  have hH : 1 ≤ H := by dsimp only [H]; exact_mod_cast integerCoefficientHeight_pos f hf
  let q := 1 / ((n + 1 : ℝ) * d * (d : ℝ) ^ (1 / (n + 1 : ℝ)))
  let C := Real.exp (2 * mertensError + 1) * hypersurfaceHeightConstant (n + 3)
  have hC : 0 ≤ C := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans (hypersurfaceHeightConstant_one_le _))
  have hbad : hypersurfaceBadPrimeFactor f ≤ C * (1 + Real.log H / (d : ℝ) ^ 2) := by
    simpa only [hdegree] using hypersurfaceBadPrimeFactor_le_height f H hH
      (coefficient_abs_le_integerCoefficientHeight f)
  have hratio : (Real.log H + (d : ℝ) ^ 2) / H ^ q ≤
      (n + 1 : ℝ) * ((Real.log Y + (d : ℝ) ^ 2) / Y ^ q) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      hypersurface_logarithmic_height_transfer (r := n + 1) (by omega) hd hY hYH
  have hstep : (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) * hypersurfaceBadPrimeFactor f / H ^ q ≤
      C * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) * ((Real.log H + (d : ℝ) ^ 2) / H ^ q) :=
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbad (by positivity))
      (by positivity)).trans_eq (by rw [rpow_four_sub_eq_mul_sq hd0 n]; field_simp; ring)
  exact hstep.trans ((mul_le_mul_of_nonneg_left hratio
    (show 0 ≤ C * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) by positivity)).trans_eq (by dsimp only [C]; ring))

end
end CCDN
