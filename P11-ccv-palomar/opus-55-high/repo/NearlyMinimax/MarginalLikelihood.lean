module

public import NearlyMinimax.HighHistoryLikelihoodScore
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Actual marginal likelihoods of latent experiments. -/
𝚹
𝚮
𝚨
𝚭
𝚩
variable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]

𝗇 𝔄 f (ω,z)
𝗇 𝔅 hf.comp $ measurable_id.prodMk measurable_const
/-- Tonelli gives the genuine density of the data marginal. -/
theorem map_snd_prod_withDensity (ν : Measure Ω) [SFinite ν] (μ : Measure Z) [SFinite μ]
    f (hf : Measurable f) :
    ((ν.prod μ).withDensity f).map Prod.snd =
      μ.withDensity fun z => ∫⁻ ω, 𝔄 ∂ν := by
  apply Measure.ext_of_lintegral
  intro G hG
  have hGm : Measurable fun z : Ω × Z => G z.2 := hG.comp measurable_snd
  rw [lintegral_map hG measurable_snd,
    lintegral_withDensity_eq_lintegral_mul _ hf hGm,
    lintegral_prod_symm' _ $ hf.mul hGm ,
    lintegral_withDensity_eq_lintegral_mul _ hf.lintegral_prod_left' hG]
  apply lintegral_congr
  intro z
  exact lintegral_mul_const (G z) 𝔅

/-- A real bounded nonnegative joint likelihood has its Bochner average
as the genuine data marginal density. -/
theorem map_snd_prod_withDensity_ofReal (ν : Measure Ω) [IsProbabilityMeasure ν]
    (μ : Measure Z) [SFinite μ] f (hf : Measurable f)
    C (hC : 𝖺₁) (hbound : ∀ z, 0 ≤ f z ∧ f z ≤ C) :
    ((ν.prod μ).withDensity fun z => ENNReal.ofReal $ f z ).map Prod.snd =
      μ.withDensity fun z => ENNReal.ofReal $ ∫ ω, 𝔄 ∂ν := by
  rw [map_snd_prod_withDensity ν μ _ hf.ennreal_ofReal]
  congr 1
  funext z
  have hi : Integrable (fun ω => 𝔄) ν := by
    apply Integrable.of_bound (𝔅).aestronglyMeasurable C
    exact Eventually.of_forall fun ω => by
      change ‖𝔄‖ ≤ C
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound _).1]
      simp_all
  exact (ofReal_integral_eq_lintegral_ofReal hi $ Eventually.of_forall fun ω => (hbound _).1 ).symm

/-- Positive actual likelihoods have a positive data marginal likelihood. -/
theorem integral_likelihood_pos (ν : Measure Ω) [IsProbabilityMeasure ν]
    f (hf : Measurable f) (C : ℝ) (hpos : ∀ ω, 0 < f ω)
    (hbound : ∀ ω, f ω ≤ C) : 0 < ∫ ω, f ω ∂ν := by
  have hi : Integrable f ν := by
    apply Integrable.of_bound hf.aestronglyMeasurable C
    exact Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos ω).le]
      exact hbound ω
  rw [integral_pos_iff_support_of_nonneg (fun ω => (hpos ω).le) hi]
  have hs : Function.support f = univ := by
    ext ω
    simp
    grind
  simp_all
