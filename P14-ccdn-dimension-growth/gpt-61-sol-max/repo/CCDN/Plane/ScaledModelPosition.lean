/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.Coordinates

import Mathlib

public import CCDN.Algebra.ScaledHomogenization
public import CCDN.Plane.LeadingPositionHeight
import CCDN.Analysis.HeightRatio
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Plane.HomogeneousLeadingCoefficient

/-!
Positioning a scaled homogeneous model while retaining a coefficient bound
for the original affine equation and the full scaling gain in its height.

A monotone scaled logarithmic-height ratio. A lower bound for the scaled
model height yields the saving needed to change the box exponent 2/d to 1/d.
-/

public section
namespace CCDN
open Real

private lemma log_height_ratio_antitone {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    (1 + v) / Real.exp v ≤ (1 + u) / Real.exp u := by
  simpa [add_comm] using weighted_exp_ratio_le hu huv zero_lt_one le_rfl (by norm_num)

/-- Eliminate an upper coefficient height in favor of any lower model height,
retaining the exact exponent 1/d² and the position loss exp(T). -/
private theorem positioned_height_ratio_le {d H L Y T : ℝ}
    (hd : 0 < d) (hY : 1 ≤ Y) (hYH : Y ≤ H) (hL : 0 < L)
    (hposition : Real.log H ≤ Real.log L + T * d ^ 2) :
    (1 + Real.log H / d ^ 2) / L ^ (1 / d ^ 2) ≤
      Real.exp T * ((1 + Real.log Y / d ^ 2) / Y ^ (1 / d ^ 2)) := by
  have hY0 : 0 < Y := by linarith
  have hds : 0 < d ^ 2 := by positivity
  have hu := div_nonneg (Real.log_nonneg hY) hds.le
  have huv :=
    div_le_div_of_nonneg_right (Real.log_le_log hY0 hYH) hds.le
  have hmono := log_height_ratio_antitone hu huv
  have hpos : Real.log H / d ^ 2 ≤ Real.log L / d ^ 2 + T := by
    apply (div_le_iff₀ hds).mpr
    field_simp
    nlinarith only [hposition]
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
    nlinarith [mul_le_mul_of_nonneg_left hexp hnum]
  have hh := hstep.trans (mul_le_mul_of_nonneg_left hmono (Real.exp_pos T).le)
  rw [Real.rpow_def_of_pos hL, Real.rpow_def_of_pos hY0]
  simpa only [mul_one_div] using hh

end CCDN

namespace CCDN
open MvPolynomial Real

/-- The model height is at least h^d and also bounds every original affine
coefficient, even after leading-coefficient positioning of the scaled model. -/
theorem exists_scaled_model_position (f : CCDN.IntegerPolynomial 2)
    (hf0 : f ≠ 0) (hd : 0 < f.totalDegree) {h : ℤ} (hh : 1 ≤ h) :
    ∃ (a : CCDN.IntPoint 2) (H : ℝ), (∀ j, 0 ≤ a j ∧ a j ≤ f.totalDegree) ∧
      1 ≤ H ∧ ↑h ^ f.totalDegree ≤ H ∧
      CoefficientHeightLE f H ∧
      Real.log |((MonomialOrder.lex.leadingCoeff
        (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f)) : ℤ) : ℝ)| ≤ Real.log H ∧
      Real.log H ≤ Real.log |((MonomialOrder.lex.leadingCoeff
        (homogeneousTranslation ℤ a (scaledHomogenize f.totalDegree h f)) : ℤ) : ℝ)| +
        14 * ↑f.totalDegree ^ 2 := by
  have hh0 : h ≠ 0 := by omega
  obtain ⟨a, H, ha, hH, hc, _, hlo, hhi⟩ := exists_translated_coefficient_position hd
    (scaledHomogenize f.totalDegree h f) (scaledHomogenize_homogeneous _ _ le_rfl)
    (scaledHomogenize_ne_zero _ hh0 hf0)
  obtain ⟨m, _, hm⟩ := exists_scaledHomogenize_top_coefficient f hf0 hh
  exact ⟨a, H, ha, hH, hm.trans (hc _),
    fun m => (scaledHomogenize_integer_coefficient_lower _ hh f m).trans (hc _), hlo, hhi⟩

/-- The exact height saving obtained from a scaling factor h. -/
theorem scaled_positioned_height_ratio_le {d : ℕ} (hd : 0 < d) {h H L : ℝ}
    (hh : 1 ≤ h) (hH : h ^ d ≤ H) (hL : 0 < L)
    (hposition : Real.log H ≤ Real.log L + 14 * ↑d ^ 2) :
    (1 + Real.log H / ↑d ^ 2) / L ^ (1 / (d : ℝ) ^ 2) ≤
      Real.exp 14 * ((1 + Real.log h / d) / h ^ (1 / (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hh0 : 0 < h := by linarith
  have hp : (h ^ d) ^ (1 / (d : ℝ) ^ 2) = h ^ (1 / (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh0.le]
    congr 1
    field_simp
  have he : Real.log (h ^ d) / ↑d ^ 2 = Real.log h / d := by
    rw [Real.log_pow]
    field_simp
  have ht := positioned_height_ratio_le hdR (one_le_pow₀ hh) hH hL hposition
  rw [hp, he] at ht
  exact ht

end CCDN
