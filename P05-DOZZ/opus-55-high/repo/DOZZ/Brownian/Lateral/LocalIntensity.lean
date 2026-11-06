/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.GlobalIndependence
public import DOZZ.GMC.Construction.GMCIntensityL1
public import Mathlib.Topology.UrysohnsLemma
public import DOZZ.Brownian.Coupling.CylindricalIntegral

/-! Exact expected local lateral measure, obtained from admissible cutoff L¹ convergence. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

open DOZZ.Assembly
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (U : Set ℂ) (dens : ℂ → ℝ)

/-- The mean of a nonnegative compact cutoff test is exactly its reference integral,
once the cutoff lies in the admissible scale range. -/
theorem admissibleCutoffIntegral_nonnegative_intensity
    (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (γ r : ℝ)
    (hr : Real.exp (-r) ≤ ε₀)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ U) (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ ω, ENNReal.ofReal (admissibleCutoffIntegral P U dens Y γ r f ω) ∂P =
      ∫⁻ x, ENNReal.ofReal (f x) ∂logRegularizationReference U dens := by
  have hint := admissibleCutoff_integrand_integrable_ae P U dens ε₀ Y hY
    (tsupport f) hfc hfU γ r hr ‖f‖ f f.continuous.measurable
    (fun x => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x)
    (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  have heq : (fun ω => ENNReal.ofReal (admissibleCutoffIntegral P U dens Y γ r f ω)) =ᵐ[P]
      fun ω => ∫⁻ x, ENNReal.ofReal (f x) *
        admissibleLogWickWeight P Y γ (Real.exp (-r)) x ω ∂logRegularizationReference U dens := by
    filter_upwards [hint] with ω hω
    rw [admissibleCutoffIntegral, ofReal_integral_eq_lintegral_ofReal hω
      (ae_of_all _ (fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le))]
    apply lintegral_congr
    intro x
    rw [ENNReal.ofReal_mul (hf0 x), ofReal_exp_eq_admissibleLogWickWeight]
  rw [lintegral_congr_ae heq]
  have hF :=
    (ENNReal.measurable_ofReal.comp (f.continuous.measurable.comp measurable_snd)).mul
      (admissibleLogWickWeight_measurable_joint P U dens ε₀ Y hY γ (Real.exp (-r)))
  rw [lintegral_lintegral_swap hF.aemeasurable]
  apply lintegral_congr
  intro x
  rw [lintegral_const_mul _ (admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY
    γ _ x), lintegral_admissibleLogWickWeight P U dens ε₀ Y hY γ
    (Real.exp (-r)) (Real.exp_pos _) hr x, mul_one]
section
variable (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ) (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (N : Ω → Measure ℂ) (hN : IsAdmissibleGMCVersion P U dens Y γ N) (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ)) (hfU : tsupport (f : ℂ → ℝ) ⊆ U)
include hY hγ hγ2 hN hfc hfU

/-- Every actual admissible version is the L¹ limit of its compact cutoff tests. -/
theorem admissibleGMCVersion_test_L1
    :
    Tendsto (fun r => ∫⁻ ω, ENNReal.ofReal |admissibleCutoffIntegral P U dens Y γ r f ω -
      ∫ x, f x ∂N ω| ∂P) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro δ hδ
  by_cases hδtop : δ = ⊤
  · simp_all
  obtain ⟨R, hR⟩ := admissibleGMCVersion_lintegral_abs_sub_le P U dens ε₀ Y hY γ hγ hγ2
    N hN f hfc hfU δ.toReal (ENNReal.toReal_pos hδ.ne' hδtop)
  aesop

/-- Compact nonnegative tests of the actual admissible limit retain the exact Wick
mean; convergence in probability is upgraded using the proved L¹ theorem. -/
theorem admissibleGMCVersion_test_intensity
    (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ ω, ENNReal.ofReal (∫ x, f x ∂N ω) ∂P =
      ∫⁻ x, ENNReal.ofReal (f x) ∂logRegularizationReference U dens := by
  let R := -Real.log ε₀
  have hR (r : ℝ) (hr : R ≤ r) : Real.exp (-r) ≤ ε₀ := by
    calc Real.exp (-r) ≤ Real.exp (-R) := Real.exp_le_exp.mpr (neg_le_neg hr)
      _ = ε₀ := by simp only [R, neg_neg, Real.exp_log hY.cutoffPositive]
  let F : ℝ → Ω → ℝ := fun r => admissibleCutoffIntegral P U dens Y γ (max r R) f
  have htop :=
    tendsto_atTop_mono (fun r => le_max_left r R) tendsto_id
  apply lintegral_ofReal_eq_of_tendsto_l1 P F (fun ω => ∫ x, f x ∂N ω)
  · intro r
    exact (admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ _ f
      f.continuous.measurable).aemeasurable
  · have hm := measurable_compact_parameter_integral (fun _ : Unit => f)
      (f.continuous.measurable.comp measurable_snd) (tsupport (f : ℂ → ℝ)) hfc
      (fun _ => subset_rfl) N hN.1 (fun ω => hN.2.2.1 ω _ hfc hfU)
    exact (hm.comp ((measurable_const : Measurable (fun _ => ())).prodMk
      measurable_id)).aemeasurable
  · intro r ω
    exact integral_nonneg (fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le)
  · intro ω
    exact integral_nonneg hf0
  · intro r
    exact admissibleCutoffIntegral_nonnegative_intensity P U dens ε₀ Y hY γ _
      (hR _ (le_max_right ..)) f hfc hfU hf0
  · exact (admissibleGMCVersion_test_L1 P U dens ε₀ Y hY γ hγ hγ2 N hN f hfc hfU).comp htop

end

end

/-- A bounded continuous compact test is integrable whenever its support has finite
measure. No global finiteness of the chart measure is required. -/
theorem integrable_compact_test_of_chart (μ : Measure ℂ)
    (f : BoundedContinuousFunction ℂ ℝ) (hfin : μ (tsupport (f : ℂ → ℝ)) < ⊤) :
    Integrable (f : ℂ → ℝ) μ := by
  have hK : MeasurableSet (tsupport (f : ℂ → ℝ)) := (isClosed_tsupport _).measurableSet
  let : IsFiniteMeasure (μ.restrict (tsupport (f : ℂ → ℝ))) :=
    isFiniteMeasure_restrict.mpr hfin.ne
  have hi : IntegrableOn (f : ℂ → ℝ) (tsupport (f : ℂ → ℝ)) μ := f.integrable (μ := μ.restrict (tsupport (f : ℂ → ℝ)))
  have heq : (tsupport (f : ℂ → ℝ)).indicator (f : ℂ → ℝ) = (f : ℂ → ℝ) := by
    funext x
    by_cases hx : x ∈ tsupport (f : ℂ → ℝ)
    · simp_all
    · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]
  rw [← heq]
  exact hi.integrable_indicator hK
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable [IsProbabilityMeasure P] (U : Set ℂ)
section
variable (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ) (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (N : Ω → Measure ℂ) (hN : IsAdmissibleGMCVersion P U dens Y γ N)
include hY hγ hγ2 hN

/-- Integrating a nonnegative compact test against the expected random measure equals
its deterministic reference integral. -/
theorem admissibleGMCVersion_expected_test_lintegral
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ U) (hf0 : ∀ x, 0 ≤ f x) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂P.bind N =
      ∫⁻ x, ENNReal.ofReal (f x) ∂logRegularizationReference U dens := by
  have hfmeas : Measurable (fun x => ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp f.continuous.measurable
  rw [Measure.lintegral_bind hN.1.aemeasurable hfmeas.aemeasurable]
  have heq : (fun ω => ∫⁻ x, ENNReal.ofReal (f x) ∂N ω) =ᵐ[P]
      fun ω => ENNReal.ofReal (∫ x, f x ∂N ω) := by
    apply ae_of_all
    intro ω
    exact (ofReal_integral_eq_lintegral_ofReal
      (integrable_compact_test_of_chart _ f (hN.2.2.1 ω _ hfc hfU))
      (ae_of_all _ hf0)).symm
  rw [lintegral_congr_ae heq]
  exact admissibleGMCVersion_test_intensity P U dens ε₀ Y hY γ hγ hγ2 N hN f hfc hfU hf0

/-- The expected admissible chaos is finite on every compact subset of its chart. -/
theorem admissibleGMCVersion_expected_compact_lt_top
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) : P.bind N K < ⊤ := by
  obtain ⟨g, hg1, hgc, hgU, hg01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK hY.openChart hKU
  let f := BoundedContinuousFunction.ofNormedAddCommGroup
    g g.continuous 1 (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg01 x).1]
      simp_all)
  have hfc : HasCompactSupport (f : ℂ → ℝ) := hasCompactSupport_def.mpr hgc
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hg01 x).1
  have heq := admissibleGMCVersion_expected_test_lintegral P U dens ε₀ Y hY γ hγ hγ2 N hN
    f hfc hgU hf0
  have hlow : P.bind N K ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂P.bind N := by
    rw [← lintegral_indicator_one hK.measurableSet]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ K
    · aesop
    simp_all
  have href : (∫⁻ x, ENNReal.ofReal (f x) ∂logRegularizationReference U dens) < ⊤ := by
    let μ := logRegularizationReference U dens
    have hfin := admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY
      (tsupport (f : ℂ → ℝ)) hfc hgU
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_compact_test_of_chart μ f hfin.lt_top) (ae_of_all _ hf0)]
    exact ENNReal.ofReal_lt_top
  exact hlow.trans_lt (heq.symm ▸ href)

end
section
variable (dens : ℂ → ℝ)
section
variable (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ) (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (N : Ω → Measure ℂ) (hN : IsAdmissibleGMCVersion P U dens Y γ N)
include hY hγ hγ2 hN

/-- The expected measure has the same signed compact-test integrals as the reference
measure, by positive and negative parts and local finiteness. -/
theorem admissibleGMCVersion_expected_signed_test
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ U) :
    (∫ x, f x ∂P.bind N) = ∫ x, f x ∂logRegularizationReference U dens := by
  have hpos : ∀ g : BoundedContinuousFunction ℂ ℝ,
      HasCompactSupport g → tsupport g ⊆ U →
      (∫⁻ x, ENNReal.ofReal (g x) ∂P.bind N) =
        ∫⁻ x, ENNReal.ofReal (g x) ∂logRegularizationReference U dens := by
    intro g hgc hgU
    let gp := g ⊔ 0
    have hs : tsupport gp ⊆ tsupport g := by
      apply closure_mono
      aesop
    have hpc :=
      hgc.isCompact.of_isClosed_subset (isClosed_tsupport _) hs
    have heq := admissibleGMCVersion_expected_test_lintegral P U dens ε₀ Y hY γ hγ hγ2 N hN
      gp hpc (hs.trans hgU) (fun x => le_max_right ..)
    aesop
  have hi := integrable_compact_test_of_chart (P.bind N) f
    (admissibleGMCVersion_expected_compact_lt_top P U dens ε₀ Y hY γ hγ hγ2 N hN
      (tsupport f) hfc hfU)
  have hr := integrable_compact_test_of_chart _ f
    (admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY
      (tsupport f) hfc hfU).lt_top
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hr, hpos f hfc hfU]
  have hnfc : HasCompactSupport ((-f)) := hfc.neg
  have hnU : tsupport ((-f)) ⊆ U := by
    simp_all
  exact congrArg (fun x =>
      (∫⁻ x, ENNReal.ofReal (f x) ∂logRegularizationReference U dens).toReal - x.toReal)
    (hpos (-f) hnfc hnU)

/-- The expected admissible chaos measure is exactly its reference measure. This is
an equality of measures, rather than merely an upper intensity bound. -/
theorem admissibleGMCVersion_expected_measure
    :
    P.bind N = logRegularizationReference U dens := by
  obtain ⟨K, hKc, hKU, _, _, hKcofinal, f, hf, hdense⟩ :=
    exists_countable_dense_admissible_tests U hY.openChart
  refine admissible_countable_tests_determine_chart_measures U hY.openChart
    (P.bind N) _ ?_ ?_
    (fun L hL hLU => admissibleGMCVersion_expected_compact_lt_top
      P U dens ε₀ Y hY γ hγ hγ2 N hN L hL hLU)
    (fun L hL hLU => (admissible_logRegularization_reference_measure_ne_top
      P U dens ε₀ Y hY L hL hLU).lt_top)
    K hKc hKU hKcofinal f (fun n m => ⟨(hf n m).1, (hf n m).2.1⟩)
    hdense (fun n m => admissibleGMCVersion_expected_signed_test P U dens ε₀ Y hY γ
      hγ hγ2 N hN _ (hf n m).1 (hf n m).2.2)
  · rw [Measure.bind_apply hY.openChart.measurableSet.compl hN.1.aemeasurable]
    simp only [hN.2.1, lintegral_zero]
  · unfold logRegularizationReference
    apply withDensity_absolutelyContinuous
    rw [Measure.restrict_apply hY.openChart.measurableSet.compl]
    simp

end

end

end
section
variable (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
section
variable (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2)) (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
include hX hc hm hcont

/-- The expected actual removed measure on each chart is the flat-cylinder plane
reference measure on that chart. -/
theorem originRadialRemovedGMC_chart_intensity
    (ρ γ : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) :
    (P.bind (fun ω => (M ω).withDensity
      (lateralRadialWeight γ (originRadialPath Xc ω)))).restrict (originLateralChart ρ) =
        logRegularizationReference (originLateralChart ρ) originLateralPlaneDensity := by
  let : IsProbabilityMeasure P := hX.1
  let F := fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))
  have hF := originRadialRemovedGMC_aemeasurable P γ
    (originRadialPath Xc) (originRadialPath_aemeasurable P X Xc hc hcont) M
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM) hM.1
  obtain ⟨N, hN, _, heq⟩ := exists_originLateralChartGMC_radial_removed_identity
    P X Xc hX hc hm hcont ρ γ hρ hγ hγ2 M hM
  have hmean := admissibleGMCVersion_expected_measure P (originLateralChart ρ)
    originLateralPlaneDensity _ _
    (originLateralCircleRegularization_admissible P X Xc hX hc hm ρ hρ)
    γ hγ hγ2 N hN
  rw [← hmean]
  apply Measure.ext
  intro S hS
  rw [Measure.restrict_apply hS, Measure.bind_apply
    (hS.inter (isOpen_originLateralChart ρ).measurableSet) hF,
    Measure.bind_apply hS hN.1.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [heq] with ω hω
  simp_all
section
variable (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include hγ hγ2 hM

/-- The entire expected removed plane measure has density `norm(x)^(-2)`.
The origin causes no atom in either measure; the countable charts determine both. -/
theorem originRadialRemovedGMC_expected_measure
    :
    P.bind (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) =
      (volume : Measure ℂ).withDensity (fun x => ENNReal.ofReal (originLateralPlaneDensity x)) := by
  let F := fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))
  have hF := originRadialRemovedGMC_aemeasurable P γ
    (originRadialPath Xc) (originRadialPath_aemeasurable P X Xc hc hcont) M
      (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM) hM.1
  apply originRadialRemovedGMC_eq_of_chart_restrictions
  · rw [Measure.bind_apply (measurableSet_singleton 0) hF]
    simp only [originRadialRemovedGMC_origin, lintegral_zero]
  · simp
  · intro n
    rw [originRadialRemovedGMC_chart_intensity P X Xc hX hc hm hcont
      (originLateralChartRadius n) γ (originLateralChartRadius_pos n) hγ hγ2 M hM,
      logRegularizationReference,
      restrict_withDensity (isOpen_originLateralChart _).measurableSet]

/-- The expected actual polar projection is the logarithmic-radius image of the flat
plane reference measure. This uses measure equality before the polar integral. -/
theorem lateralProjectedGMC_expected_measure
    :
    P.bind (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) =
      ((volume : Measure ℂ).withDensity (fun x => ENNReal.ofReal
        (originLateralPlaneDensity x))).map (fun x => -Real.log ‖x‖) := by
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hlog : Measurable (fun x : ℂ => -Real.log ‖x‖) :=
    by fun_prop
  rw [← originRadialRemovedGMC_expected_measure P X Xc hX hc hm hcont γ hγ hγ2 M hM]
  apply Measure.ext
  intro S hS
  rw [Measure.bind_apply hS (lateralProjectedGMC_aemeasurable P γ (originRadialPath Xc) hA M hMm hM.1), Measure.map_apply hlog hS,
    Measure.bind_apply (hS.preimage hlog) (originRadialRemovedGMC_aemeasurable P γ (originRadialPath Xc) hA M hMm hM.1)]
  apply lintegral_congr
  intro ω
  exact Measure.map_apply hlog hS

end

end

end

end
section
variable (F : ℝ → ℝ≥0∞)




/-- Complex polar coordinates for a general nonnegative radial test. -/
theorem lintegral_complex_norm (hF : Measurable F) :
    (∫⁻ z : ℂ, F ‖z‖) = ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal r * F r := by
  have heq (r : ℝ) (hr : 0 ≤ r) : cylindricalRadius 0 r = r := by
    simp only [cylindricalRadius, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add,
      Real.sqrt_sq_eq_abs, abs_of_nonneg hr]
  have h := lintegral_complex_cylindricalRadius 0 F hF
  simp_rw [heq _ (norm_nonneg _)] at h
  rw [h]
  congr 1
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro r hr
  grind

/-- The substitution `r = exp(-s)` converts the radial density `1/r` into Lebesgue
measure on the whole logarithmic cylinder, with both signs of `s` included. -/
theorem lintegral_logRadius_jacobian :
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r⁻¹) * F (-Real.log r)) = ∫⁻ s : ℝ, F s := by
  have himage : (fun s => Real.exp (-s)) '' univ = Ioi 0 := by
    ext r
    constructor
    · rintro ⟨s, _, rfl⟩
      exact Real.exp_pos _
    · intro hr
      exact ⟨-Real.log r, mem_univ _, by dsimp only; rw [neg_neg, Real.exp_log hr]⟩
  have hderiv (s : ℝ) : HasDerivAt (fun t => Real.exp (-t)) (-Real.exp (-s)) s := by
    simpa using (hasDerivAt_neg s).exp
  have hinj : InjOn (fun s => Real.exp (-s)) univ := by
    intro s _ t _ h
    simp_all
  have h := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun s _ => (hderiv s).hasDerivWithinAt) hinj
    (fun r => ENNReal.ofReal (r⁻¹) * F (-Real.log r))
  rw [himage, Measure.restrict_univ] at h
  rw [h]
  apply lintegral_congr
  intro s
  rw [abs_neg, abs_of_pos (Real.exp_pos _), ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    mul_inv_cancel₀ (Real.exp_pos _).ne', ENNReal.ofReal_one, one_mul,
    Real.log_exp, neg_neg]

/-- The radial density of the removed chaos gives exactly the flat cylinder
reference, including the angular factor `2π`. -/
theorem lintegral_flatLateralReference_logRadius
    (hF : Measurable F) :
    (∫⁻ x, F (-Real.log ‖x‖) ∂(volume : Measure ℂ).withDensity
      (fun x => ENNReal.ofReal (originLateralPlaneDensity x))) =
        ENNReal.ofReal (2 * Real.pi) * ∫⁻ s : ℝ, F s := by
  have hd : Measurable (fun x : ℂ => ENNReal.ofReal (originLateralPlaneDensity x)) := by
    unfold originLateralPlaneDensity
    fun_prop
  have hf : Measurable (fun x : ℂ => F (-Real.log ‖x‖)) :=
    by fun_prop
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hf]
  let G : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (-2 : ℝ)) * F (-Real.log r)
  have hG : Measurable G := by
    fun_prop
  change (∫⁻ x : ℂ, G ‖x‖) = _
  rw [lintegral_complex_norm G hG]
  have heq : (∫⁻ r in Ioi 0, ENNReal.ofReal r * G r) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r⁻¹) * F (-Real.log r) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp [G]
    have halg : r * r ^ (-2 : ℝ) = r⁻¹ := by
      rw [Real.rpow_neg hr.le, Real.rpow_two]
      field_simp
    rw [← mul_assoc, ← ENNReal.ofReal_mul hr.le, halg]
  rw [heq, lintegral_logRadius_jacobian]

end

/-- The logarithmic-radius image of the planar reference is exactly `2π` times
Lebesgue measure, as a full equality of measures. -/
theorem flatLateralReference_logRadius :
    ((volume : Measure ℂ).withDensity (fun x => ENNReal.ofReal
      (originLateralPlaneDensity x))).map (fun x => -Real.log ‖x‖) =
        ENNReal.ofReal (2 * Real.pi) • (volume : Measure ℝ) := by
  have hlog : Measurable (fun x : ℂ => -Real.log ‖x‖) :=
    by fun_prop
  apply Measure.ext
  intro S hS
  have h := lintegral_flatLateralReference_logRadius (S.indicator 1)
    (measurable_const.indicator hS)
  have hmap := lintegral_map (μ := volume.withDensity
    (fun x => ENNReal.ofReal (originLateralPlaneDensity x)))
   
    (f := S.indicator 1)
    (measurable_const.indicator hS) hlog
  simp_all
section
variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
section
variable (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc) (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2)) (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2)) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
include hX hc hm hcont hγ hγ2 hM

/-- Exact expected measure of the actual projected chaos on the entire cylinder. -/
theorem lateralProjectedGMC_expected_flat_measure
    :
    P.bind (fun ω => lateralProjectedGMC γ (originRadialPath Xc ω) (M ω)) =
      ENNReal.ofReal (2 * Real.pi) • (volume : Measure ℝ) := by
  rw [lateralProjectedGMC_expected_measure P X Xc hX hc hm hcont γ hγ hγ2 M hM,
    flatLateralReference_logRadius]

/-- The actual projected chaos has the exact interval intensity required by the lateral
predicate `DOZZ.IsLateralGMCOf`. This is proved before stationarity or any moment
theorem is used. -/
theorem lateralProjectedGMC_interval_intensity
    (a b : ℝ) :
    ∫⁻ ω, lateralProjectedGMC γ (originRadialPath Xc ω) (M ω) (Ioc a b) ∂P =
      ENNReal.ofReal (2 * Real.pi * (b - a)) := by
  have hZ := lateralProjectedGMC_aemeasurable P γ (originRadialPath Xc) (originRadialPath_aemeasurable P X Xc hc hcont) M
    (equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM) hM.1
  rw [← Measure.bind_apply measurableSet_Ioc hZ,
    lateralProjectedGMC_expected_flat_measure P X Xc hX hc hm hcont γ hγ hγ2 M hM,
    Measure.smul_apply, smul_eq_mul, Real.volume_Ioc,
    ← ENNReal.ofReal_mul (mul_pos (by norm_num) Real.pi_pos).le]

end

end

end DOZZ.Proofs
