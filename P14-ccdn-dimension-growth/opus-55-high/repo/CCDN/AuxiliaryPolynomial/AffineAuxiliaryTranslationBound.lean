/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.AuxiliaryPolynomial.PrimeScaledAffineMinimum
import CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight
import CCDN.ForMathlib.Log

/-! Translating the affine box by a vector bounded by the degree costs only
 a dimension constant in the coefficient-sensitive minimum bound. -/

namespace CCDN

lemma affine_box_translation_power {r d : ℕ} (hr : 0 < r) (hd : 0 < d)
    {B : ℝ} (hB : 1 ≤ B) :
    (B + d) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) ≤
      Real.exp ((r : ℝ) + 1) * B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hfactor : ((d : ℝ) + 1) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) ≤
      Real.exp ((r : ℝ) + 1) := by
    rw [Real.rpow_def_of_pos (by positivity), Real.exp_le_exp, ← div_eq_mul_one_div]
    exact (div_le_iff₀ (by positivity)).mpr (log_nat_add_one_le_root hr hd)
  calc
    _ ≤ (((d : ℝ) + 1) * B) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := by
      apply Real.rpow_le_rpow (by positivity) _ (by positivity)
      nlinarith
    _ = ((d : ℝ) + 1) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) *
        B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := Real.mul_rpow (by positivity) (by linarith)
    _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)

section
variable {d : ℕ} (hd : 0 < d)
include hd

lemma affine_box_translation_log {B : ℝ} (hB : 1 ≤ B) :
    Real.log (B + d) ≤ Real.log B + Real.log ((d : ℝ) + 1) := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hlog := Real.log_le_log (by positivity : 0 < B + d)
    (show B + d ≤ B * ((d : ℝ) + 1) by nlinarith)
  rwa [Real.log_mul (by linarith) (by positivity)] at hlog

lemma affine_box_translation_min
    {B L b : ℝ} (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    min (Real.log L + d * Real.log (B + d) + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) ≤
      2 * min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) := by
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hlogd := Real.log_add_one_le_self d.cast_nonneg
  have hnum : Real.log L + d * Real.log (B + d) + d ^ 2 ≤
      2 * (Real.log L + d * Real.log B + d ^ 2) := by
    have hlog := affine_box_translation_log hd hB
    have hLlog := Real.log_nonneg hL
    have hBlog := Real.log_nonneg hB
    nlinarith
  rcases le_total (Real.log L + d * Real.log B + d ^ 2) (d ^ 2 * b) with h | h
  · grind
  · rw [min_eq_right h]
    exact (min_le_right _ _).trans (by nlinarith)

end

section
variable {r d : ℕ}

end

/-- Specialization to the common minimum bound used by both affine branches. -/
theorem affineMinimumAuxiliaryBound_translation {n d : ℕ} (hd : 0 < d)
    {A B L b : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    affineMinimumAuxiliaryBound n d A (B + d) L b ≤
      (2 * Real.exp ((n : ℝ) + 2)) * affineMinimumAuxiliaryBound n d A B L b := by
  have hK : 0 ≤ max (affineHeightTransferConstant n) (Real.exp 1) * A :=
    mul_nonneg ((Real.exp_pos 1).le.trans (le_max_right _ _)) hA
  have hd0 : (0 : ℝ) < d := mod_cast hd
  have hLlog := Real.log_nonneg hL
  have hBlog := Real.log_nonneg hB
  have hBp : 1 ≤ B + d := by linarith
  have hBplog := Real.log_nonneg hBp
  have hmin0 : 0 ≤ min (Real.log L + d * Real.log B + d ^ 2) (d ^ 2 * b) := by
    positivity
  have hminp0 : 0 ≤ min (Real.log L + d * Real.log (B + d) + d ^ 2)
      ((d : ℝ) ^ 2 * b) := by positivity
  have hmain := mul_le_mul (affine_box_translation_min hd hB hL hb)
    (affine_box_translation_power (r := n + 1) (by omega) hd hB) (by positivity)
    (show 0 ≤ 2 * min (Real.log L + d * Real.log B + (d : ℝ) ^ 2)
      ((d : ℝ) ^ 2 * b) by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hmain
    (show 0 ≤ max (affineHeightTransferConstant n) (Real.exp 1) * A * (d : ℝ) ^ (2 - 1 / (n + 1 : ℝ)) /
      L ^ (1 / ((n + 1 : ℝ) * d * d ^ (1 / (n + 1 : ℝ)))) by positivity)
  have hlower : d ^ (1 - 1 / ((n + 1) : ℝ)) * Real.log (B + d) +
        (d : ℝ) ^ (4 - 1 / ((n + 1) : ℝ)) ≤
      2 * (d ^ (1 - 1 / ((n + 1) : ℝ)) * Real.log B +
        (d : ℝ) ^ (4 - 1 / ((n + 1) : ℝ))) := by
    have hd1 : (1 : ℝ) ≤ d := mod_cast hd
    have hd0 : (0 : ℝ) < d := by linarith
    have hlogd := Real.log_add_one_le_self d.cast_nonneg
    have hpow : (d : ℝ) ^ (1 - 1 / ((n + 1) : ℝ)) * d ≤ (d : ℝ) ^ (4 - 1 / ((n + 1) : ℝ)) := by
      calc
        _ = (d : ℝ) ^ (2 - 1 / ((n + 1) : ℝ)) := by
          calc
            _ = (d : ℝ) ^ (1 - 1 / ((n + 1) : ℝ)) * (d : ℝ) ^ (1 : ℝ) := by simp_all
            _ = _ := by rw [← Real.rpow_add hd0]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
    have hlog := affine_box_translation_log hd hB
    have hdlow : 0 ≤ (d : ℝ) ^ (1 - 1 / ((n + 1) : ℝ)) := by positivity
    nlinarith
  have hE : 1 ≤ Real.exp ((n : ℝ) + 2) := Real.one_le_exp (by positivity)
  have hnonneg : 0 ≤ d ^ (1 - 1 / (n + 1 : ℝ)) * Real.log B +
      (d : ℝ) ^ (4 - 1 / (n + 1 : ℝ)) := by positivity
  have hcost := mul_le_mul_of_nonneg_right hE hnonneg
  simp only [one_mul] at hcost
  have hcost2 := mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 2)
  push_cast at hscaled hlower
  unfold affineMinimumAuxiliaryBound
  convert mul_le_mul_of_nonneg_left (add_le_add hscaled (hlower.trans hcost2))
    (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le using 1 <;> ring_nf

