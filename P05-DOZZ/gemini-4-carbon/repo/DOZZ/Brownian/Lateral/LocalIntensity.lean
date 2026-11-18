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

variable {Ω : Type*} [MeasurableSpace Ω]

open DOZZ.Assembly

private lemma int_bcf (μ : Measure ℂ) (f : BoundedContinuousFunction ℂ ℝ)
    (hfin : μ (tsupport (f : ℂ → ℝ)) < ⊤) : Integrable (f : ℂ → ℝ) μ := by
  let : IsFiniteMeasure (μ.restrict (tsupport (f : ℂ → ℝ))) := isFiniteMeasure_restrict.mpr hfin.ne
  have hi : IntegrableOn (f : ℂ → ℝ) (tsupport (f : ℂ → ℝ)) μ :=
    f.integrable (μ := μ.restrict (tsupport (f : ℂ → ℝ)))
  refine (hi.integrable_indicator (isClosed_tsupport _).measurableSet).congr (ae_of_all _ fun x => ?_)
  by_cases hx : x ∈ tsupport (f : ℂ → ℝ)
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx]

private lemma expected_admissible_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : Ω → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y)
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (N : Ω → Measure ℂ)
    (hN : IsAdmissibleGMCVersion P U dens Y γ N) :
    P.bind N = logRegularizationReference U dens := by
  have hlint (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
      (hfU : tsupport (f : ℂ → ℝ) ⊆ U) (hf0 : ∀ x, 0 ≤ f x) :
      ∫⁻ x, ENNReal.ofReal (f x) ∂P.bind N =
        ∫⁻ x, ENNReal.ofReal (f x) ∂logRegularizationReference U dens := by
    have hfm : Measurable fun x : ℂ => ENNReal.ofReal (f x) :=
      ENNReal.measurable_ofReal.comp f.continuous.measurable
    rw [Measure.lintegral_bind hN.1.aemeasurable hfm.aemeasurable,
      lintegral_congr_ae (ae_of_all _ fun ω => (ofReal_integral_eq_lintegral_ofReal
        (int_bcf _ f (hN.2.2.1 ω _ hfc hfU)) (ae_of_all _ hf0)).symm)]
    let R := -Real.log ε₀
    refine lintegral_ofReal_eq_of_tendsto_l1 P
      (fun r => admissibleCutoffIntegral P U dens Y γ (max r R) f) (fun ω => ∫ x, f x ∂N ω) _
      (fun r => (admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ _ f
        f.continuous.measurable).aemeasurable)
      (((measurable_compact_parameter_integral (fun _ : Unit => f)
        (f.continuous.measurable.comp measurable_snd) _ hfc (fun _ => subset_rfl) N hN.1
        fun ω => hN.2.2.1 ω _ hfc hfU).comp
          ((measurable_const : Measurable fun _ : Ω => ()).prodMk measurable_id)).aemeasurable)
      (fun _ _ => integral_nonneg fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le)
      (fun _ => integral_nonneg hf0) (fun r => ?_) ?_
    · have hr : Real.exp (-max r R) ≤ ε₀ := (Real.exp_le_exp.mpr
        (neg_le_neg (le_max_right r R))).trans_eq (by simp [R, Real.exp_log hY.cutoffPositive])
      have hint := admissibleCutoff_integrand_integrable_ae P U dens ε₀ Y hY _ hfc hfU γ
        (max r R) hr ‖f‖ f f.continuous.measurable
        (fun x => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x)
        fun _ => image_eq_zero_of_notMem_tsupport
      have heq : (fun ω => ENNReal.ofReal (admissibleCutoffIntegral P U dens Y γ (max r R) f ω))
          =ᵐ[P] fun ω => ∫⁻ x, ENNReal.ofReal (f x) *
            admissibleLogWickWeight P Y γ (Real.exp (-max r R)) x ω ∂logRegularizationReference U dens := by
        filter_upwards [hint] with ω hω
        rw [admissibleCutoffIntegral, ofReal_integral_eq_lintegral_ofReal hω
          (ae_of_all _ fun x => mul_nonneg (hf0 x) (Real.exp_pos _).le)]
        exact lintegral_congr fun x => by
          rw [ENNReal.ofReal_mul (hf0 x), ofReal_exp_eq_admissibleLogWickWeight]
      rw [lintegral_congr_ae heq, lintegral_lintegral_swap (((ENNReal.measurable_ofReal.comp
          (f.continuous.measurable.comp measurable_snd)).mul
          (admissibleLogWickWeight_measurable_joint P U dens ε₀ Y hY γ _)).aemeasurable)]
      exact lintegral_congr fun x => by
        rw [lintegral_const_mul _ (admissibleLogWickWeight_measurable_sample P U dens ε₀ Y hY γ _ x),
          lintegral_admissibleLogWickWeight P U dens ε₀ Y hY γ _ (Real.exp_pos _) hr x, mul_one]
    · refine (show Tendsto (fun r : ℝ => ∫⁻ ω, ENNReal.ofReal
          |admissibleCutoffIntegral P U dens Y γ r f ω - ∫ x, f x ∂N ω| ∂P) atTop (𝓝 0) from
        ENNReal.tendsto_nhds_zero.mpr fun δ hδ => ?_).comp
        (tendsto_atTop_mono (fun r => le_max_left r R) tendsto_id)
      by_cases hδtop : δ = ⊤
      · exact Eventually.of_forall fun _ => hδtop ▸ le_top
      obtain ⟨R', hR'⟩ := admissibleGMCVersion_lintegral_abs_sub_le P U dens ε₀ Y hY γ hγ hγ2
        N hN f hfc hfU δ.toReal (ENNReal.toReal_pos hδ.ne' hδtop)
      filter_upwards [eventually_ge_atTop R'] with r hr
      exact (hR' r hr).trans_eq (ENNReal.ofReal_toReal hδtop)
  have hcomp (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U) : P.bind N K < ⊤ := by
    obtain ⟨g, hg1, hgc, hgU, hg01⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hY.openChart hKU
    let f := BoundedContinuousFunction.ofNormedAddCommGroup g g.continuous 1 fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg01 x).1]; exact (hg01 x).2
    have hfc := hasCompactSupport_def.mpr hgc
    refine (le_trans ?_ (hlint f hfc hgU fun x => (hg01 x).1).le).trans_lt ?_
    · rw [← lintegral_indicator_one hK.measurableSet]
      refine lintegral_mono fun x => ?_
      by_cases hx : x ∈ K
      · rw [indicator_of_mem hx]; change 1 ≤ ENNReal.ofReal (g x); simp [hg1 hx]
      · simp [hx]
    · rw [← ofReal_integral_eq_lintegral_ofReal (int_bcf _ f
        (admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY _ hfc hgU).lt_top)
        (ae_of_all _ fun x => (hg01 x).1)]
      exact ENNReal.ofReal_lt_top
  have hpos (g : BoundedContinuousFunction ℂ ℝ) (hgc : HasCompactSupport (g : ℂ → ℝ))
      (hgU : tsupport (g : ℂ → ℝ) ⊆ U) :
      (∫⁻ x, ENNReal.ofReal (g x) ∂P.bind N) =
        ∫⁻ x, ENNReal.ofReal (g x) ∂logRegularizationReference U dens := by
    let gp := g ⊔ 0
    have hs : tsupport (gp : ℂ → ℝ) ⊆ tsupport (g : ℂ → ℝ) :=
      closure_mono fun x hx h0 => hx (show max (g x) 0 = 0 by simp [h0])
    simpa only [show ∀ x, ENNReal.ofReal (gp x) = ENNReal.ofReal (g x) from fun x => by
      change ENNReal.ofReal (max (g x) 0) = _; simp] using
      hlint gp (hgc.isCompact.of_isClosed_subset (isClosed_tsupport _) hs) (hs.trans hgU)
        fun _ => le_max_right _ _
  obtain ⟨K, hKc, hKU, _, _, hKcofinal, f, hf, hdense⟩ :=
    exists_countable_dense_admissible_tests U hY.openChart
  refine admissible_countable_tests_determine_chart_measures U hY.openChart (P.bind N) _ ?_ ?_
    hcomp (fun L hL hLU => (admissible_logRegularization_reference_measure_ne_top
      P U dens ε₀ Y hY L hL hLU).lt_top) K hKc hKU hKcofinal f
    (fun n m => ⟨(hf n m).1, (hf n m).2.1⟩) hdense (fun n m => ?_)
  · rw [Measure.bind_apply hY.openChart.measurableSet.compl hN.1.aemeasurable]
    simp [hN.2.1]
  · refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply hY.openChart.measurableSet.compl]; simp
  · rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part
        (int_bcf _ _ (hcomp _ (hf n m).1 (hf n m).2.2)),
      integral_eq_lintegral_pos_part_sub_lintegral_neg_part (int_bcf _ _
        (admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY _
          (hf n m).1 (hf n m).2.2).lt_top),
      hpos _ (hf n m).1 (hf n m).2.2]
    exact congrArg (fun x : ℝ≥0∞ => _ - x.toReal)
      (hpos (-f (n, m)) (hf n m).1.neg (by simpa using (hf n m).2.2))

/-- The actual projected chaos has the exact interval intensity required by the lateral
predicate `DOZZ.IsLateralGMCOf`. This is proved before stationarity or any moment
theorem is used. -/
theorem lateralProjectedGMC_interval_intensity
    (P : Measure Ω) (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M) (a b : ℝ) :
    ∫⁻ ω, lateralProjectedGMC γ (originRadialPath Xc ω) (M ω) (Ioc a b) ∂P =
      ENNReal.ofReal (2 * Real.pi * (b - a)) := by
  let : IsProbabilityMeasure P := hX.1
  have hA := originRadialPath_aemeasurable P X Xc hc hcont
  have hMm := equatorGFF_GMC_aemeasurable P X hX γ hγ hγ2 M hM
  have hF := originRadialRemovedGMC_aemeasurable P γ (originRadialPath Xc) hA M hMm hM.1
  have hrem : P.bind (fun ω => (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω))) =
      (volume : Measure ℂ).withDensity fun x => ENNReal.ofReal (originLateralPlaneDensity x) := by
    refine originRadialRemovedGMC_eq_of_chart_restrictions _ _ ?_
      (withDensity_absolutelyContinuous _ _ (measure_singleton 0)) fun n => ?_
    · rw [Measure.bind_apply (measurableSet_singleton (0 : ℂ)) hF]
      change (∫⁻ ω, (M ω).withDensity (lateralRadialWeight γ (originRadialPath Xc ω)) {0} ∂P) = 0
      simp only [originRadialRemovedGMC_origin, lintegral_zero]
    · set ρ := originLateralChartRadius n
      have hρ := originLateralChartRadius_pos n
      obtain ⟨N, hN, _, heq⟩ := exists_originLateralChartGMC_radial_removed_identity
        P X Xc hX hc hm hcont ρ γ hρ hγ hγ2 M hM
      rw [restrict_withDensity (isOpen_originLateralChart ρ).measurableSet, ← logRegularizationReference,
        ← expected_admissible_eq P _ _ (min ρ 1) _
          (originLateralCircleRegularization_admissible P X Xc hX hc hm ρ hρ) γ hγ hγ2 N hN]
      ext S hS
      rw [Measure.restrict_apply hS, Measure.bind_apply
        (hS.inter (isOpen_originLateralChart ρ).measurableSet) hF, Measure.bind_apply hS hN.1.aemeasurable]
      refine lintegral_congr_ae ?_
      filter_upwards [heq] with ω hω
      rw [hω, Measure.restrict_apply hS]
  have hlog : Measurable fun x : ℂ => -Real.log ‖x‖ :=
    measurable_neg.comp (Real.measurable_log.comp measurable_norm)
  let F : ℝ → ℝ≥0∞ := (Ioc a b).indicator 1
  have hFm : Measurable F := measurable_const.indicator measurableSet_Ioc
  have hFl : Measurable fun x : ℂ => F (-Real.log ‖x‖) := hFm.comp hlog
  have hlhs : (∫⁻ ω, lateralProjectedGMC γ (originRadialPath Xc ω) (M ω) (Ioc a b) ∂P) =
      ∫⁻ x, F (-Real.log ‖x‖) ∂(volume : Measure ℂ).withDensity
        fun x => ENNReal.ofReal (originLateralPlaneDensity x) := by
    rw [← hrem, Measure.lintegral_bind hF hFl.aemeasurable]
    refine lintegral_congr fun ω => ?_
    rw [lateralProjectedGMC, Measure.map_apply hlog measurableSet_Ioc, ← lintegral_indicator_one
      (measurableSet_Ioc.preimage hlog)]
    rfl
  rw [hlhs, lintegral_withDensity_eq_lintegral_mul _ (by unfold originLateralPlaneDensity; fun_prop)
    hFl]
  let G : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (r ^ (-2 : ℝ)) * F (-Real.log r)
  have hG : Measurable G := by fun_prop
  have hpol := lintegral_complex_cylindricalRadius 0 G hG
  have hrad (r : ℝ) (hr : 0 ≤ r) : cylindricalRadius 0 r = r := by
    simp [cylindricalRadius, Real.sqrt_sq_eq_abs, abs_of_nonneg hr]
  simp_rw [hrad _ (norm_nonneg _)] at hpol
  change (∫⁻ x : ℂ, G ‖x‖) = _
  rw [hpol, setLIntegral_congr_fun (g := fun r => ENNReal.ofReal r⁻¹ * F (-Real.log r))
    measurableSet_Ioi fun r (hr : 0 < r) => by
    dsimp only; rw [hrad r hr.le]; dsimp only [G]
    rw [← mul_assoc, ← ENNReal.ofReal_mul hr.le,
      show r * r ^ (-2 : ℝ) = r⁻¹ by rw [Real.rpow_neg hr.le, Real.rpow_two]; field_simp]]
  have himg : (fun s : ℝ => Real.exp (-s)) '' univ = Ioi (0 : ℝ) := by
    ext r; exact ⟨by rintro ⟨s, _, rfl⟩; exact Real.exp_pos _,
      fun hr => ⟨-Real.log r, trivial, by dsimp; rw [neg_neg, Real.exp_log hr]⟩⟩
  have hjac := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun s _ => ((by simpa using (hasDerivAt_neg s).exp :
      HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-s)) s)).hasDerivWithinAt)
    (fun s _ t _ h => neg_injective (Real.exp_injective h))
    fun r => ENNReal.ofReal r⁻¹ * F (-Real.log r)
  rw [himg, Measure.restrict_univ] at hjac
  rw [hjac, lintegral_congr fun s => by
    rw [abs_neg, abs_of_pos (Real.exp_pos _), ← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      mul_inv_cancel₀ (Real.exp_pos _).ne', ENNReal.ofReal_one, one_mul, Real.log_exp, neg_neg]]
  rw [lintegral_indicator_one measurableSet_Ioc, Real.volume_Ioc,
    ← ENNReal.ofReal_mul (by positivity)]

end DOZZ.Proofs
