module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaLegendreDual

@[expose] public section

/-!
# Quantitative stability of the inverse model slope

The first dual derivative is compared with the reciprocal-exponent reference
on the actual slope image. The constants come from the original model error
and its derived curvature lower bound, not from an assumed inverse estimate.
-/

noncomputable section

open Set Expdb
open scoped ContDiff

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

theorem approximateModelPhase_firstDeriv_error {σ δ : ℝ} {P : ℕ} {F : ℝ → ℝ}
    (hF : IsApproximateModelPhaseFunction F σ P δ)
    {u : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) :
    |deriv F u - u^(-σ)| ≤ δ := by
  have he := hF.2 0 (Nat.zero_le P) ⟨u, hu.1.le, hu.2.le⟩
  have hc : ContDiffAt ℝ 1 F u :=
    (approximateModelPhase_contDiffAt hF hu).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  change ‖iteratedDerivWithin 1 F phaseInterval u - modelPhase σ u‖ ≤ δ at he
  rw [iteratedDerivWithin_eq_iteratedDeriv
    uniqueDiffOn_phaseInterval hc ⟨hu.1.le,hu.2.le⟩] at he
  simpa only [iteratedDeriv_one, modelPhase,
    Real.norm_eq_abs] using he

theorem approximateModelPhase_slope_gap {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u w : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (hw : w ∈ Ioo (1 : ℝ) 2)
    (huw : u ≤ w) :
    modelPhaseCurvatureLower σ * (w-u) ≤ deriv F u - deriv F w := by
  have hc : ContinuousOn (deriv F) (Ioo (1 : ℝ) 2) := fun x hx =>
    (approximateModelPhase_deriv_contDiffAt hF hx).continuousAt.continuousWithinAt
  have hd : DifferentiableOn ℝ (deriv F) (interior (Ioo (1 : ℝ) 2)) := by
    intro x hx
    exact ((approximateModelPhase_deriv_contDiffAt hF (by simpa using hx)).differentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)).differentiableWithinAt
  have hb : ∀ x ∈ interior (Ioo (1 : ℝ) 2),
      deriv (deriv F) x ≤ -modelPhaseCurvatureLower σ := by
    intro x hx
    have h := (approximateModelPhase_curvature_deriv_bounds hσ hδ hF
      (by simpa using hx)).1
    linarith
  have hg := (convex_Ioo (1 : ℝ) 2).image_sub_le_mul_sub_of_deriv_le
    hc hd hb u hu w hw huw
  linarith

theorem approximateModelPhase_slope_gap_abs {σ δ : ℝ} {F : ℝ → ℝ}
    (hσ : 0 < σ) (hδ : δ ≤ min (modelPhaseCurvatureLower σ) 1)
    (hF : IsApproximateModelPhaseFunction F σ 1 δ)
    {u w : ℝ} (hu : u ∈ Ioo (1 : ℝ) 2) (hw : w ∈ Ioo (1 : ℝ) 2) :
    modelPhaseCurvatureLower σ * |u-w| ≤ |deriv F u - deriv F w| := by
  have hm := (approximateModelPhase_deriv_strictAntiOn hσ hδ hF).antitoneOn
  rcases le_total u w with huw | hwu
  · rw [abs_of_nonpos (sub_nonpos.mpr huw),
      abs_of_nonneg (sub_nonneg.mpr (hm hu hw huw))]
    have hg := approximateModelPhase_slope_gap hσ hδ hF hu hw huw
    nlinarith
  · rw [abs_of_nonneg (sub_nonneg.mpr hwu),
      abs_of_nonpos (sub_nonpos.mpr (hm hw hu hwu))]
    have hg := approximateModelPhase_slope_gap hσ hδ hF hw hu hwu
    nlinarith

theorem reciprocal_modelPhase_identity {σ v : ℝ} (hσ : 0 < σ) (hv : 0 ≤ v) :
    (v^(-σ⁻¹))^(-σ) = v := by
  rw [← Real.rpow_mul hv, neg_mul_neg, inv_mul_cancel₀ hσ.ne', Real.rpow_one]

end TaoTrudgianYang2025
