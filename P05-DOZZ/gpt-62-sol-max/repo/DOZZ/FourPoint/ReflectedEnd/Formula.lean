/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.FourPoint.GammaHalfReflectedOuterLittleO
public import DOZZ.Statements.FourPoint.FourPointTZeroEqStructureConstant
public import DOZZ.FourPoint.Reflected.Normalization
public import DOZZ.FourPoint.Reflected.Remainder
import Mathlib.Tactic
public import DOZZ.FourPoint.Dual.DiagonalReduction
public import DOZZ.Statements.FourPoint.GammaHalfReflectedInnerLimit
public import DOZZ.Statements.FourPoint.DegenerateFourPointDiagonalClassification

/-! The reflected formula follows from the inner limit `DOZZ.gammaHalf_reflected_inner_limit` and
the physical diagonal classification `DOZZ.degenerateFourPoint_diagonal_classification`. -/

@[expose] public section
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The real part of a complex reflected remainder has the signed little-o limit. -/
private theorem reflected_real_part_remainder (κ : ℝ) (r : ℂ → ℂ)
    (hr : IsComplexLittleOAtZero κ r) :
    Tendsto (fun z => (r z).re / ‖z‖ ^ κ)
      (nhdsWithin (0 : ℂ) {z : ℂ | z ≠ 0}) (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have he : (fun z => ‖(r z).re / ‖z‖ ^ κ‖) =
      fun z => |(r z).re| / ‖z‖ ^ κ := by
    funext z
    rw [norm_div, Real.norm_eq_abs, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
  rw [he]
  exact squeeze_zero (fun z => div_nonneg (abs_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))
    (fun z => div_le_div_of_nonneg_right (Complex.abs_re_le_norm (r z))
      (Real.rpow_nonneg (norm_nonneg _) _)) hr

/-- The exact reflected formula in the physical frame, with the original reflection data. -/
theorem gammaHalf_reflected_formula {Ω : Type*} [MeasurableSpace Ω]
    {H : ℂ → ℂ → ℂ → ℂ → ℂ}
    (hH : IsGaussHypergeometricFamily H)
    (P : Measure Ω) (M : Ω → Measure ℂ) (X : Ω → Distr)
    (γ μ α₁ α₂ α₃ : ℝ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hμ : 0 < μ)
    (hα₁ : α₁ < Q γ) (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ)
    (hs : 2 * Q γ + γ / 2 < α₁ + α₂ + α₃)
    (hreflect : Q γ - α₁ < γ / 2)
    (hnear : ∃ ξ : ℝ, 0 < ξ ∧ ξ < 1 ∧ γ * (Q γ - α₁) < ξ ∧
      γ * (Q γ - α₁) < (1 - ξ) * (γ * (Q γ - α₁) + (α₁ + γ / 2 - Q γ) ^ 2 / 2))
    (hX : IsEquatorGFF P X) (hM : IsGMCOf P X γ M) :
    ∃ B : ℝ → Ω → BrownianPath × BrownianPath,
      ∃ Z : Ω → Measure ℝ,
        IsSourceLateralProjection P X γ M Z ∧
        IsReflectionData P γ α₁ (B α₁) Z ∧
        let a := gaussParameterA γ (γ / 2) α₁ α₂ α₃
        let b := gaussParameterB γ (γ / 2) α₁ α₂ α₃
        let c := gaussParameterC γ (γ / 2) α₁
        ∀ z ∈ gaussCutPlane,
          fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
            structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃ *
                ‖gaussFMinus H a b c z‖ ^ 2 +
              reflectionR P γ μ α₁ (B α₁) Z *
                structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃ *
                  ‖gaussFPlus H a b c z‖ ^ 2 := by
  obtain ⟨ξ, hξ, hξ₂, hslack, hfreeze⟩ := hnear
  have hinner := DOZZ.gammaHalf_reflected_inner_limit P M X γ μ α₁ α₂ α₃ ξ
    hγ hγ₂ hμ hα₁ hα₂ hα₃ hs hξ hξ₂ hreflect
    (lt_min (hslack.trans hξ₂) hslack) hfreeze hX hM
  obtain ⟨B, Z, hZ, hB, rI, hI, hrI⟩ := hinner
  let p  := (α₁ + α₂ + α₃ - γ / 2 - 2 * Q γ) / γ
  let κ  := γ * (Q γ - α₁)
  let N  := 2 * μ ^ (-p) / γ * Real.Gamma p
  let D  := reflectionR P γ μ α₁ (B α₁) Z *
    structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃
  let C₀  := structureConstant P M γ μ (α₁ - γ / 2) α₂ α₃
  let r  := fun z => fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z - C₀ - D * ‖z‖ ^ κ
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have hT (z : ℂ) : fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z =
      N * gammaHalfMoment P M γ α₁ α₂ α₃ p z := by
    simpa only [neg_div] using fourPointT_eq_gammaHalfMoment P M γ μ α₁ α₂ α₃ z
  have hzero : N * gammaHalfMoment P M γ α₁ α₂ α₃ p 0 = C₀ := by
    rw [← hT 0]
    simpa only [neg_div] using DOZZ.fourPointT_zero_eq_structureConstant P X M γ μ (γ / 2) α₁ α₂ α₃
      hγ hγ₂ hμ (by linarith) hα₂ hα₃ (by linarith only [hs]) hX hM
  have hcancel := reflected_prefactor_cancel γ μ p
    (reflectionR P γ μ α₁ (B α₁) Z)
    (structureConstant P M γ μ (2 * Q γ - α₁ - γ / 2) α₂ α₃) hγ hμ hp
  have hr (z : ℂ) : r z = N *
      (gammaHalfOuterMoment P M γ α₁ α₂ α₃ p z ξ -
        gammaHalfMoment P M γ α₁ α₂ α₃ p 0 + (rI z).re) := by
    have hh := congrArg Complex.re (hI z)
    simp only [Complex.ofReal_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_im, mul_zero, sub_zero] at hh
    dsimp only [r]
    rw [hT z, ← hzero]
    linear_combination N * hh + (‖z‖ ^ κ) * hcancel
  have hlim : Tendsto (fun z => r z / ‖z‖ ^ κ) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have ho := DOZZ.gammaHalf_reflected_outer_littleO P X M γ α₁ α₂ α₃ ξ
      hγ hγ₂ hξ hξ₂ hα₂ hα₃ hs hα₁ hreflect hslack hfreeze hX hM
    have hor := (isComplexLittleOAtZero_ofReal_iff κ _).mp ho
    have hir := reflected_real_part_remainder κ rI hrI
    have ht := (hor.add hir).const_mul N
    simp only [add_zero, mul_zero] at ht
    apply ht.congr'
    filter_upwards [] with z
    rw [hr z]
    ring
  have hclassification := DOZZ.degenerateFourPoint_diagonal_classification hH
    P X M γ μ (γ / 2) α₁ α₂ α₃ hγ hγ₂ hμ
    (Or.inl rfl) hα₁ hα₂ hα₃ hs hX hM
  have hκ : κ < 1 := hslack.trans hξ₂
  have hcast : Tendsto (fun t : ℝ => (t : ℂ))
      (nhdsWithin 0 (Ioi 0)) (nhdsWithin 0 {z : ℂ | z ≠ 0}) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_id.mono_left nhdsWithin_le_nhds), ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simpa only [Complex.ofReal_ne_zero] using ne_of_gt ht
  have hrl : Tendsto (fun t : ℝ => r (t : ℂ) / t ^ κ)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    apply (hlim.comp hcast).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Function.comp_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  have hray : Tendsto (fun t : ℝ =>
      (fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ (t : ℂ) - C₀) / t ^ κ)
      (nhdsWithin 0 (Ioi 0)) (nhds D) := by
    have ht := hrl.const_add D
    simp only [add_zero] at ht
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    dsimp only [r]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hn : t ^ κ ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
    field_simp
    ring
  dsimp only at hclassification ⊢
  obtain ⟨hA, hAB, hBC, hC, _, _, _, _⟩ := DOZZ.gauss_physical_parameter_range
    γ (γ / 2) α₁ α₂ α₃ hγ hγ₂ (Or.inl rfl) hs hα₁ hα₂ hα₃
  have hc : 0 < gaussParameterC γ (γ / 2) α₁ := hA.trans (hAB.trans hBC)
  have he : 2 * (1 - gaussParameterC γ (γ / 2) α₁) = κ := by
    unfold gaussParameterC
    dsimp only [κ]
    ring
  have hid := dual_diagonal_coefficient_identification hH
    (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
    (gaussParameterB γ (γ / 2) α₁ α₂ α₃)
    (gaussParameterC γ (γ / 2) α₁) C₀
    (gaussCoefficientRatio (gaussParameterA γ (γ / 2) α₁ α₂ α₃)
      (gaussParameterB γ (γ / 2) α₁ α₂ α₃) (gaussParameterC γ (γ / 2) α₁)) D
    hc hC (he ▸ hκ) (fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃)
    (by simpa only [neg_div] using hclassification) (by simpa only [he] using hray)
  refine ⟨B, Z, hZ, hB, ?_⟩
  intro z hz
  rw [show fourPointT P M γ μ (-γ / 2) α₁ α₂ α₃ z = _ from
    by simpa only [neg_div] using hclassification z hz]
  change C₀ * (_ + _ * _) = C₀ * _ + D * _
  rw [hid]
  ring

end DOZZ.Proofs
