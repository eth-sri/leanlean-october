module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Convolution by a probability density is an `Lᵖ` contraction -/

@[expose] public section

open MeasureTheory
open scoped Convolution ENNReal

namespace PDE

theorem isProbabilityMeasure_withDensity_ofReal
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ρ : α → ℝ}
    (hρNonneg : ∀ x, 0 ≤ ρ x)
    (hρInt : Integrable ρ μ)
    (hρOne : ∫ x, ρ x ∂μ = 1) :
    IsProbabilityMeasure
      (μ.withDensity fun x => ENNReal.ofReal (ρ x)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hρInt
    (ae_of_all _ hρNonneg), hρOne]
  simp

/-- On a probability space, the extended `p`th moment bounds the `p`th power
    of the norm of the expectation, with no integrability side conditions. -/
private lemma enorm_integral_rpow_le {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsProbabilityMeasure ν] {f : X → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ⊤)
    (hf : AEStronglyMeasurable f ν) :
    ‖∫ t, f t ∂ν‖ₑ ^ p.toReal ≤ ∫⁻ t, ‖f t‖ₑ ^ p.toReal ∂ν := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hp' := ENNReal.toReal_pos hp₀ hpTop
  have h : ‖∫ t, f t ∂ν‖ₑ ≤ eLpNorm f p ν :=
    (enorm_integral_le_lintegral_enorm f).trans
      ((eLpNorm_one_eq_lintegral_enorm hf).ge.trans (eLpNorm_le_eLpNorm_of_exponent_le hp))
  have hpow := ENNReal.rpow_le_rpow h hp'.le
  rwa [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hpTop hf,
    ← ENNReal.rpow_mul, one_div_mul_cancel hp'.ne', ENNReal.rpow_one] at hpow

variable {G : Type*} [AddCommGroup G] [MeasurableSpace G]
  [MeasurableAdd₂ G] [MeasurableNeg G] {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]

section
variable {ρ g : G → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpTop : p ≠ ⊤) (hρ₀ : ∀ t, 0 ≤ ρ t)
  (hρi : Integrable ρ μ) (hρ₁ : ∫ t, ρ t ∂μ = 1) (hρ : Measurable ρ)
include hp hpTop hρ₀ hρi hρ₁ hρ

private lemma convolution_contract_measurable (hg : Measurable g) :
    eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) p μ ≤ eLpNorm g p μ := by
  let ν := μ.withDensity fun t => ENNReal.ofReal (ρ t)
  let _ : IsProbabilityMeasure ν := isProbabilityMeasure_withDensity_ofReal hρ₀ hρi hρ₁
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hconv := hρi.aestronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hg.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hpTop hconv,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hpTop hg.aestronglyMeasurable]
  apply ENNReal.rpow_le_rpow _ (by positivity)
  let F : G → ℝ≥0∞ := fun y => ‖g y‖ₑ ^ p.toReal
  have hF : Measurable F := hg.enorm.pow_const _
  have hpoint (x : G) : (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x =
      ∫ t, g (x - t) ∂ν := by
    unfold ν
    rw [integral_withDensity_eq_integral_toReal_smul hρ.ennreal_ofReal
      (.of_forall fun _ => ENNReal.ofReal_lt_top)]
    simp [convolution_def, ENNReal.toReal_ofReal, hρ₀, smul_eq_mul]
  have htranslate (t : G) : (∫⁻ x, F (x - t) ∂μ) = ∫⁻ x, F x ∂μ := by
    simp_rw [sub_eq_add_neg]
    rw [← lintegral_map hF (measurable_add_const (-t)), map_add_right_eq_self]
  calc
    _ ≤ ∫⁻ x, ∫⁻ t, F (x - t) ∂ν ∂μ := lintegral_mono fun x => by
      rw [hpoint]
      exact enorm_integral_rpow_le hp hpTop ((hg.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    _ = ∫⁻ t, ∫⁻ x, F (x - t) ∂μ ∂ν :=
      lintegral_lintegral_swap (hF.comp (measurable_fst.sub measurable_snd)).aemeasurable
    _ = _ := by simp_rw [htranslate]; simp [F]

/-- Convolution by a nonnegative kernel of integral one is contractive in
    every finite `Lᵖ` seminorm with `p ≥ 1`. -/
theorem eLpNorm_convolution_le_of_integral_one (hg : AEMeasurable g μ) :
    eLpNorm (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) p μ ≤ eLpNorm g p μ := by
  rw [convolution_congr _ Filter.EventuallyEq.rfl hg.ae_eq_mk, eLpNorm_congr_ae hg.ae_eq_mk]
  exact convolution_contract_measurable hp hpTop hρ₀ hρi hρ₁ hρ hg.measurable_mk

end

end PDE
