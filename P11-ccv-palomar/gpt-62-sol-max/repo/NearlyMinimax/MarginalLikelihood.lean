module

public import NearlyMinimax.HighHistoryLikelihoodScore


@[expose] public section

/-! Actual marginal likelihoods of latent experiments. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]

section
variable (ν : Measure Ω)

/-- Tonelli gives the genuine density of the data marginal. -/
theorem map_snd_prod_withDensity [SFinite ν] (μ : Measure Z) [SFinite μ]
    (f : Ω × Z → ℝ≥0∞) (hf : Measurable f) :
    ((ν.prod μ).withDensity f).map Prod.snd =
      μ.withDensity (fun z => ∫⁻ ω, f (ω,z) ∂ν) := by
  apply Measure.ext_of_lintegral
  intro G hG
  have hfm : Measurable (fun z => ∫⁻ ω, f (ω,z) ∂ν) := hf.lintegral_prod_left'
  have hGm : Measurable (fun z : Ω × Z => G z.2) := hG.comp measurable_snd
  rw [lintegral_map hG measurable_snd,
    lintegral_withDensity_eq_lintegral_mul _ hf hGm,
    lintegral_prod_symm' _ (hf.mul hGm),
    lintegral_withDensity_eq_lintegral_mul _ hfm hG]
  apply lintegral_congr
  intro z
  exact lintegral_mul_const (G z) (hf.comp (measurable_id.prodMk measurable_const))

/-- A real bounded nonnegative joint likelihood has its Bochner average
as the genuine data marginal density. -/
theorem map_snd_prod_withDensity_ofReal [IsProbabilityMeasure ν]
    (μ : Measure Z) [SFinite μ] (f : Ω × Z → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ z, 0 ≤ f z ∧ f z ≤ C) :
    ((ν.prod μ).withDensity (fun z => ENNReal.ofReal (f z))).map Prod.snd =
      μ.withDensity (fun z => ENNReal.ofReal (∫ ω, f (ω,z) ∂ν)) := by
  rw [map_snd_prod_withDensity ν μ _ hf.ennreal_ofReal]
  congr 1
  funext z
  have hi : Integrable (fun ω => f (ω,z)) ν := by
    apply Integrable.of_bound (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable C
    exact Eventually.of_forall fun ω => by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hbound _).1] using (hbound _).2
  exact (ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun ω => (hbound _).1)).symm

/-- Positive actual likelihoods have a positive data marginal likelihood. -/
theorem integral_likelihood_pos [IsProbabilityMeasure ν]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hpos : ∀ ω, 0 < f ω)
    (hbound : ∀ ω, f ω ≤ C) : 0 < ∫ ω, f ω ∂ν := by
  have hi : Integrable f ν := by
    apply Integrable.of_bound hf.aestronglyMeasurable C
    exact Eventually.of_forall fun ω => by
      simp_all [Real.norm_eq_abs, abs_of_nonneg (hpos ω).le]
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hi]
  have hs : Function.support f = univ := by
    ext ω
    simpa using (hpos ω).ne'
  simp [hs]

end

end NearlyMinimax
