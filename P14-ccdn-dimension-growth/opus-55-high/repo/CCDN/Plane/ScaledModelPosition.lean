/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.ScaledHomogenization
import CCDN.Plane.LeadingPositionHeight
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Plane.HomogeneousLeadingCoefficient

/-!
Positioning a scaled homogeneous model while retaining a coefficient bound
for the original affine equation and the full scaling gain in its height.

A monotone scaled logarithmic-height ratio. A lower bound for the scaled
model height yields the saving needed to change the box exponent 2/d to 1/d.
-/

namespace CCDN
open Real

lemma log_height_ratio_antitone {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (1 + v) / Real.exp v ≤ (1 + u) / Real.exp u := by
  have he : 1 + (v - u) ≤ Real.exp (v - u) := by
    simpa [add_comm] using Real.add_one_le_exp (v - u)
  have hh : 1 + v ≤ (1 + u) * Real.exp (v - u) := by nlinarith
  apply (div_le_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)).mpr
  have hp := mul_le_mul_of_nonneg_right hh (Real.exp_pos u).le
  rwa [mul_assoc, ← Real.exp_add, sub_add_cancel] at hp

/-- Eliminate an upper coefficient height in favor of any lower model height,
retaining the exact exponent 1/d² and the position loss exp(T). -/
theorem positioned_height_ratio_le {d H L Y T : ℝ}
    (hd : 0 < d) (hY : 1 ≤ Y) (hYH : Y ≤ H) (hL : 0 < L)
    (hposition : Real.log H ≤ Real.log L + T * d ^ 2) :
    (1 + Real.log H / d ^ 2) / L ^ (1 / d ^ 2) ≤
      Real.exp T * ((1 + Real.log Y / d ^ 2) / Y ^ (1 / d ^ 2)) := by
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  have hds : 0 < d ^ 2 := by positivity
  have hu := div_nonneg (Real.log_nonneg hY) hds.le
  have huv :=
    div_le_div_of_nonneg_right (Real.log_le_log hY0 hYH) hds.le
  have hmono := log_height_ratio_antitone hu huv
  have hpos : Real.log H / d ^ 2 ≤ Real.log L / d ^ 2 + T := by
    field_simp
    grind
  have hexp : Real.exp (Real.log H / d ^ 2) ≤
      Real.exp T * Real.exp (Real.log L / d ^ 2) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hnum : 0 ≤ 1 + Real.log H / d ^ 2 := by linarith
  have hstep : (1 + Real.log H / d ^ 2) / Real.exp (Real.log L / d ^ 2) ≤
      Real.exp T * ((1 + Real.log H / d ^ 2) / Real.exp (Real.log H / d ^ 2)) := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    rw [← mul_div_assoc, div_mul_eq_mul_div]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    nlinarith
  have hh := hstep.trans (mul_le_mul_of_nonneg_left hmono (Real.exp_pos T).le)
  rw [Real.rpow_def_of_pos hL, Real.rpow_def_of_pos hY0]
  simpa only [mul_one_div] using hh

end CCDN

namespace CCDN
open MvPolynomial Real

/-- The model height is at least h^d and also bounds every original affine
coefficient, even after leading-coefficient positioning of the scaled model. -/
theorem exists_scaled_model_position (f : MvPolynomial (Fin 2) ℤ)
    (hf0 : f ≠ 0) (hd : 0 < f.totalDegree) {h : ℤ} (hh : 1 ≤ h) :
    ∃ (a : Fin 2 → ℤ) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ f.totalDegree) ∧
      1 ≤ H ∧ (h : ℝ) ^ f.totalDegree ≤ H ∧
      CoefficientHeightLE f H ∧
      Real.log |((MonomialOrder.lex.leadingCoeff
        (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f)) : ℤ) : ℝ)| ≤ Real.log H ∧
      Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff
        (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f)) : ℤ) : ℝ)| +
        14 * (f.totalDegree : ℝ) ^ 2 := by
  have hh0 : h ≠ 0 := by omega
  obtain ⟨a, H, ha, hH, hc, -, hlo, hhi⟩ := exists_translated_coefficient_position hd
    (scaledHomogenize f.totalDegree h f) (scaledHomogenize_homogeneous _ _ le_rfl)
    (scaledHomogenize_ne_zero _ hh0 hf0)
  obtain ⟨m, hm⟩ := exists_scaledHomogenize_top_coefficient f hf0 hh
  exact ⟨a, H, ha, hH, hm.trans (hc _),
    fun m => (show |(f.coeff m : ℝ)| ≤ |((scaledHomogenize _ h f).coeff (homogenizedExponent _ m) : ℝ)| by
        have hhR : (1 : ℝ) ≤ h := mod_cast hh
        rw [scaledHomogenize_coefficient, Int.cast_mul, Int.cast_pow, abs_mul, abs_pow,
          abs_of_nonneg (by linarith : (0 : ℝ) ≤ h)]
        have hp := one_le_pow₀ (n := m.sum (fun _ e => e)) hhR
        nlinarith [abs_nonneg (f.coeff m : ℝ)]).trans (hc _), hlo, hhi⟩

/-- The exact height saving obtained from a scaling factor h. -/
theorem scaled_positioned_height_ratio_le {d : ℕ} (hd : 0 < d) {h H L : ℝ}
    (hh : 1 ≤ h) (hH : h ^ d ≤ H) (hL : 0 < L)
    (hposition : Real.log H ≤ Real.log L + 14 * (d : ℝ) ^ 2) :
    (1 + Real.log H / (d : ℝ) ^ 2) / L ^ (1 / (d : ℝ) ^ 2) ≤
      Real.exp 14 * ((1 + Real.log h / d) / h ^ (1 / (d : ℝ))) := by
  have hh0 : 0 < h := by linarith
  have hp : (h ^ d) ^ (1 / (d : ℝ) ^ 2) = h ^ (1 / (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh0.le]
    grind
  have he : Real.log (h ^ d) / d ^ 2 = Real.log h / d := by
    rw [Real.log_pow]
    field_simp
  have ht := positioned_height_ratio_le (mod_cast hd) (one_le_pow₀ hh) hH hL hposition
  rwa [hp, he] at ht

