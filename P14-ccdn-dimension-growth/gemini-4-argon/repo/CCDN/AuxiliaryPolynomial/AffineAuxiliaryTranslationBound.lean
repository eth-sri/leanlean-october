/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.AuxiliaryPolynomial.PrimeScaledAffineMinimum
import CCDN.AuxiliaryPolynomial.HypersurfacePositionHeight
import CCDN.ForMathlib.Log

/-! Translating the affine box by a vector bounded by the degree costs only
 a dimension constant in the coefficient-sensitive minimum bound. -/

@[expose] public section
namespace CCDN
noncomputable section

/-- Specialization to the common minimum bound used by both affine branches. -/
theorem affineMinimumAuxiliaryBound_translation {n d : ℕ} (hd : 0 < d)
    {A B L b : ℝ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hL : 1 ≤ L) (hb : 0 ≤ b) :
    affineMinimumAuxiliaryBound n d A (B + d) L b ≤
      (2 * Real.exp ((n : ℝ) + 2)) * affineMinimumAuxiliaryBound n d A B L b := by
  let r := n + 1
  have hr : 0 < r := by omega
  have hd1 : (1 : ℝ) ≤ d := mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hlogd : Real.log ((d : ℝ) + 1) ≤ d := Real.log_add_one_le_self d.cast_nonneg
  have hLlog := Real.log_nonneg hL
  have hBlog := Real.log_nonneg hB
  have hlog : Real.log (B + d) ≤ Real.log B + Real.log ((d : ℝ) + 1) := by
    rw [← Real.log_mul (by linarith) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hpow_box : (B + d) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) ≤
      Real.exp ((r : ℝ) + 1) * B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) := by
    have hfactor : ((d : ℝ) + 1) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) ≤ Real.exp ((r : ℝ) + 1) := by
      rw [Real.rpow_def_of_pos (by positivity), Real.exp_le_exp, ← div_eq_mul_one_div]
      exact (div_le_iff₀ (by positivity)).mpr (log_nat_add_one_le_root hr hd)
    calc (B + d) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ)))
      _ ≤ (((d : ℝ) + 1) * B) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) :=
        Real.rpow_le_rpow (by positivity) (by nlinarith) (by positivity)
      _ = ((d : ℝ) + 1) ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) * B ^ (1 / (d : ℝ) ^ (1 / (r : ℝ))) :=
        Real.mul_rpow (by positivity) (by linarith)
      _ ≤ _ := mul_le_mul_of_nonneg_right hfactor (by positivity)
  have hmin : min (Real.log L + d * Real.log (B + d) + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) ≤
      2 * min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) := by
    have hnum : Real.log L + d * Real.log (B + d) + (d : ℝ) ^ 2 ≤
        2 * (Real.log L + d * Real.log B + (d : ℝ) ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hlog hd0.le, mul_le_mul_of_nonneg_left hlogd hd0.le]
    rcases le_total (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) with h | h
    · rw [min_eq_left h]; exact (min_le_left _ _).trans hnum
    · rw [min_eq_right h]; exact (min_le_right _ _).trans (by nlinarith [sq_nonneg (d : ℝ)])
  have hlower : (d : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log (B + d) + (d : ℝ) ^ (4 - 1 / (r : ℝ)) ≤
      2 * ((d : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log B + (d : ℝ) ^ (4 - 1 / (r : ℝ))) := by
    have hpow : (d : ℝ) ^ (1 - 1 / (r : ℝ)) * d ≤ (d : ℝ) ^ (4 - 1 / (r : ℝ)) := calc
      (d : ℝ) ^ (1 - 1 / (r : ℝ)) * d = (d : ℝ) ^ (1 - 1 / (r : ℝ)) * (d : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (d : ℝ) ^ (2 - 1 / (r : ℝ)) := by rw [← Real.rpow_add hd0]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hd1 (by linarith)
    have hdlow : 0 ≤ (d : ℝ) ^ (1 - 1 / (r : ℝ)) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlog hdlow, mul_le_mul_of_nonneg_left hlogd hdlow]
  let K := max (affineHeightTransferConstant n) (Real.exp 1) * A
  have hK : 0 ≤ K := mul_nonneg ((Real.exp_pos 1).le.trans (le_max_right _ _)) hA
  have hBp : 1 ≤ B + d := by linarith
  have hBplog := Real.log_nonneg hBp
  have hmain := mul_le_mul hmin hpow_box (by positivity)
    (show 0 ≤ 2 * min (Real.log L + d * Real.log B + (d : ℝ) ^ 2) ((d : ℝ) ^ 2 * b) by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hmain
    (show 0 ≤ K * (d : ℝ) ^ (2 - 1 / (r : ℝ)) /
      L ^ (1 / ((r : ℝ) * d * (d : ℝ) ^ (1 / (r : ℝ)))) by positivity)
  have hE : 1 ≤ Real.exp ((r : ℝ) + 1) := Real.one_le_exp (by positivity)
  have hcost := mul_le_mul_of_nonneg_right hE
    (show 0 ≤ (d : ℝ) ^ (1 - 1 / (r : ℝ)) * Real.log B + (d : ℝ) ^ (4 - 1 / (r : ℝ)) by positivity)
  simp only [one_mul] at hcost
  have hcost2 := mul_le_mul_of_nonneg_left hcost (by norm_num : (0 : ℝ) ≤ 2)
  have hh := add_le_add hscaled (hlower.trans hcost2)
  dsimp only [r, K] at hh
  simp only [Nat.cast_add, Nat.cast_one, show (n : ℝ) + 1 + 1 = n + 2 by ring] at hh
  have hfinal := mul_le_mul_of_nonneg_left hh (hypersurfaceAbsoluteAuxiliaryConstant_pos n).le
  unfold affineMinimumAuxiliaryBound
  convert hfinal using 1 <;> ring

end
end CCDN
