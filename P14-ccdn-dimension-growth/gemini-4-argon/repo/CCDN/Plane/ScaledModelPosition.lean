/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Algebra.ScaledHomogenization
public import CCDN.Plane.LeadingPositionHeight
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CCDN.Plane.HomogeneousLeadingCoefficient

/-!
Positioning a scaled homogeneous model while retaining a coefficient bound
for the original affine equation and the full scaling gain in its height.

A monotone scaled logarithmic-height ratio. A lower bound for the scaled
model height yields the saving needed to change the box exponent 2/d to 1/d.
-/

@[expose] public section
namespace CCDN
noncomputable section
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
  let d := f.totalDegree
  let F := scaledHomogenize d h f
  have hF : F.IsHomogeneous d := scaledHomogenize_homogeneous _ _ le_rfl
  obtain ⟨a, ha, hne, hcoeff⟩ := exists_bounded_leading_coefficient_translation F hF
    (scaledHomogenize_ne_zero _ (by omega) hf0)
  let L := |((MonomialOrder.lex.leadingCoeff (homogeneousTranslation ℤ a F) : ℤ) : ℝ)|
  have hL : 1 ≤ L := by dsimp only [L]; exact_mod_cast Int.one_le_abs hne
  have hP := leadingPositionHeightFactor_one_le d
  have hpos : 0 < leadingPositionHeightFactor d := by linarith
  have hLpos : 0 < L := by linarith
  have hint : ((d : ℝ) + 1) ^ (2 * (d + 1)) ≤ leadingPositionHeightFactor d := by
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have h₁ : 1 ≤ ((d : ℝ) + 2) ^ 2 := one_le_pow₀ (by linarith)
    have h₂ : 1 ≤ (2 * (d : ℝ) + 1) ^ d := one_le_pow₀ (by linarith)
    have hp := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ d + 1)
      (show 2 * (d + 1) ≤ 4 * (d + 1) by omega)
    unfold leadingPositionHeightFactor
    nlinarith [show 0 ≤ ((d : ℝ) + 1) ^ (4 * (d + 1)) by positivity,
      mul_le_mul_of_nonneg_left h₁ (show 0 ≤ ((d : ℝ) + 1) ^ (4 * (d + 1)) by positivity)]
  have hc : CoefficientHeightLE F (leadingPositionHeightFactor d * L) :=
    fun m => (hcoeff m).trans (mul_le_mul_of_nonneg_right hint hLpos.le)
  obtain ⟨m, _, hm⟩ := exists_scaledHomogenize_top_coefficient f hf0 hh
  refine ⟨a, leadingPositionHeightFactor d * L, ha, one_le_mul_of_one_le_of_one_le hP hL,
    hm.trans (hc _), fun m => (scaledHomogenize_integer_coefficient_lower _ hh f m).trans (hc _),
    Real.log_le_log hLpos (by nlinarith), ?_⟩
  rw [Real.log_mul hpos.ne' hLpos.ne']
  linarith [leadingPositionHeightFactor_log_le hd]

/-- The exact height saving obtained from a scaling factor h. -/
theorem scaled_positioned_height_ratio_le {d : ℕ} (hd : 0 < d) {h H L : ℝ}
    (hh : 1 ≤ h) (hH : h ^ d ≤ H) (hL : 0 < L)
    (hposition : Real.log H ≤ Real.log L + 14 * (d : ℝ) ^ 2) :
    (1 + Real.log H / (d : ℝ) ^ 2) / L ^ (1 / (d : ℝ) ^ 2) ≤
      Real.exp 14 * ((1 + Real.log h / d) / h ^ (1 / (d : ℝ))) := by
  have hdR : (0 : ℝ) < d := mod_cast hd
  have hh0 : 0 < h := by linarith
  let Y := h ^ d
  have hY : 1 ≤ Y := one_le_pow₀ hh
  have hY0 : 0 < Y := by linarith
  have hH0 : 0 < H := by linarith
  have hds : 0 < (d : ℝ) ^ 2 := by positivity
  let u := Real.log Y / (d : ℝ) ^ 2
  let v := Real.log H / (d : ℝ) ^ 2
  have hu : 0 ≤ u := div_nonneg (Real.log_nonneg hY) hds.le
  have huv : u ≤ v := div_le_div_of_nonneg_right (Real.log_le_log hY0 hH) hds.le
  have he : 1 + (v - u) ≤ Real.exp (v - u) := by
    simpa only [add_comm] using Real.add_one_le_exp (v - u)
  have hh_uv : 1 + v ≤ (1 + u) * Real.exp (v - u) := by
    nlinarith [mul_le_mul_of_nonneg_left he (show 0 ≤ 1 + u by linarith),
      mul_nonneg hu (sub_nonneg.mpr huv)]
  have hp_uv := mul_le_mul_of_nonneg_right hh_uv (Real.exp_pos u).le
  rw [mul_assoc, ← Real.exp_add, sub_add_cancel] at hp_uv
  have hmono : (1 + v) / Real.exp v ≤ (1 + u) / Real.exp u :=
    (div_le_div_iff₀ (Real.exp_pos _) (Real.exp_pos _)).mpr hp_uv
  have hpos : v ≤ Real.log L / (d : ℝ) ^ 2 + 14 :=
    (div_le_iff₀ hds).mpr (by rw [add_mul, div_mul_cancel₀ _ hds.ne']; linarith)
  have hexp : Real.exp v ≤ Real.exp 14 * Real.exp (Real.log L / (d : ℝ) ^ 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
  have hstep : (1 + v) / Real.exp (Real.log L / (d : ℝ) ^ 2) ≤
      Real.exp 14 * ((1 + v) / Real.exp v) := by
    rw [div_le_iff₀ (Real.exp_pos _), ← mul_div_assoc, div_mul_eq_mul_div,
      le_div_iff₀ (Real.exp_pos _)]
    nlinarith [mul_le_mul_of_nonneg_left hexp (show 0 ≤ 1 + v by linarith)]
  have hfinal := hstep.trans (mul_le_mul_of_nonneg_left hmono (Real.exp_pos 14).le)
  have hp : Y ^ (1 / (d : ℝ) ^ 2) = h ^ (1 / (d : ℝ)) := by
    change (h ^ d) ^ (1 / (d : ℝ) ^ 2) = h ^ (1 / (d : ℝ))
    rw [← Real.rpow_natCast, ← Real.rpow_mul hh0.le]; congr 1; field_simp
  have he_u : u = Real.log h / d := by
    change Real.log (h ^ d) / (d : ℝ) ^ 2 = Real.log h / d
    rw [Real.log_pow]; field_simp
  rw [← hp, ← he_u, Real.rpow_def_of_pos hL, Real.rpow_def_of_pos hY0]
  simpa only [v, mul_one_div] using hfinal

end
end CCDN
