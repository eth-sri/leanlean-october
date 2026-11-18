/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.Lateral.WickReinsertion
public import DOZZ.GMC.CompatibleAdmissibleGMCUnique

/-!
# Uniform compact changes of a Wick test
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Distributions InnerProductSpace RealInnerProductSpace

namespace DOZZ.Proofs

variable {Ω : Type*} [MeasurableSpace Ω]

open DOZZ.Assembly

private lemma continuous_circleIntegral_banach
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : ℂ → E) (hF : Continuous F) :
    Continuous (fun p : ℂ × ℝ => ∫ z, F z ∂circleMeasure p.1 p.2) := by
  have hi : Continuous (fun p : ℂ × ℝ =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), F (circleMap p.1 (Real.exp (-p.2)) θ)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hF.comp (by fun_prop [circleMap])
  have heq : (fun p : ℂ × ℝ => ∫ z, F z ∂circleMeasure p.1 p.2) =
      fun p => (2 * Real.pi)⁻¹ • ∫ θ in (0 : ℝ)..(2 * Real.pi), F (circleMap p.1 (Real.exp (-p.2)) θ) :=
    funext fun p => by
      rw [circleMeasure, integral_smul_measure,
        integral_map (measurable_circleMap p.1 (Real.exp (-p.2))).aemeasurable hF.aestronglyMeasurable,
        ← intervalIntegral.integral_of_le Real.two_pi_pos.le,
        ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
  rw [heq]; exact continuous_const.smul hi

/-- The finite radial factor is jointly continuous in the entire continuous path,
center and logarithmic cutoff. Evaluation is continuous on the compact-open path space. -/
theorem continuous_originRadialCutoffReinsertionWeight_joint (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ γ : ℝ) (hρ : 0 < ρ) :
    Continuous (fun p : TwoSidedPath × (ℂ × ℝ) =>
      originRadialCutoffReinsertionWeight hc ρ γ p.2.2 p.1 p.2.1) := by
  have hR : Continuous (fun p : TwoSidedPath × (ℂ × ℝ) => originCircleRadialL2 hc ρ p.2.1 p.2.2) :=
    (continuous_circleIntegral_banach _ (continuous_clampedRadialCircleL2 P X Xc hX hc ρ hρ)).comp continuous_snd
  have hv : Continuous (fun p : TwoSidedPath × (ℂ × ℝ) =>
      gaussianVariance P (originCircleRadialL2 hc ρ p.2.1 p.2.2)) := by
    have heq : (fun p : TwoSidedPath × (ℂ × ℝ) =>
        gaussianVariance P (originCircleRadialL2 hc ρ p.2.1 p.2.2)) =
        fun p => ⟪originCircleRadialL2 hc ρ p.2.1 p.2.2, originCircleRadialL2 hc ρ p.2.1 p.2.2⟫_ℝ :=
      funext fun _ => by unfold gaussianVariance gaussianCovariance; rw [integral_mul_eq_inner]
    rw [heq]; exact hR.inner hR
  have hi : Continuous (fun p : TwoSidedPath × (ℂ × ℝ) =>
      ∫ θ in (0 : ℝ)..(2 * Real.pi), p.1 (clampedLogRadius ρ (circleMap p.2.1 (Real.exp (-p.2.2)) θ))) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact continuous_eval.comp (continuous_fst.fst.prodMk ((continuous_clampedLogRadius ρ hρ).comp
      (by fun_prop [circleMap] : Continuous fun p : (TwoSidedPath × (ℂ × ℝ)) × ℝ =>
        circleMap p.1.2.1 (Real.exp (-p.1.2.2)) p.2)))
  have ha : Continuous (fun p : TwoSidedPath × (ℂ × ℝ) =>
      ∫ z, p.1 (clampedLogRadius ρ z) ∂circleMeasure p.2.1 p.2.2) := by
    have heq : (fun p : TwoSidedPath × (ℂ × ℝ) =>
        ∫ z, p.1 (clampedLogRadius ρ z) ∂circleMeasure p.2.1 p.2.2) =
        fun p => (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          p.1 (clampedLogRadius ρ (circleMap p.2.1 (Real.exp (-p.2.2)) θ)) :=
      funext fun p => by
        rw [integral_circleMeasure_eq_circleAverage p.2.1 p.2.2 (fun z => p.1 (clampedLogRadius ρ z))
          (p.1.continuous.comp (continuous_clampedLogRadius ρ hρ)).measurable, Real.circleAverage_def]
        rfl
    rw [heq]; exact hi.const_mul _
  exact (((ha.const_mul γ).sub (hv.const_mul (γ ^ 2 / 2))).sub
    (((continuous_clampedLogRadius ρ hρ).comp continuous_snd.fst).abs.const_mul 2)).rexp

/-- The literal finite radial-weighted compact test, with no change of its variance. -/
noncomputable def originRadialCutoffWeightedTest (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ γ r : ℝ) (hρ : 0 < ρ) (A : TwoSidedPath)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ)) :
    BoundedContinuousFunction ℂ ℝ := by
  let F : ℂ → ℝ := fun x => f x * originRadialCutoffReinsertionWeight hc ρ γ r A x
  have hF : Continuous F := f.continuous.mul
    ((continuous_originRadialCutoffReinsertionWeight_joint P X Xc hX hc ρ γ hρ).comp
      ((continuous_const : Continuous fun _ : ℂ => A).prodMk
        (continuous_id.prodMk (continuous_const : Continuous fun _ : ℂ => r))))
  have hb := hF.bounded_above_of_compact_support hfc.mul_right
  exact BoundedContinuousFunction.ofNormedAddCommGroup F hF hb.choose hb.choose_spec

private lemma varying_test_tendstoInMeasure {E : Type*} [MeasurableSpace E]
    (P : Measure E) [IsProbabilityMeasure P]
    (U : Set ℂ) (dens : ℂ → ℝ) (ε₀ : ℝ) (Y : E → ℝ → ℂ → ℝ)
    (hY : IsAdmissibleLogRegularization P U dens ε₀ Y) (γ : ℝ)
    (N : E → Measure ℂ) (hN : IsAdmissibleGMCVersion P U dens Y γ N)
    (K : Set ℂ) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : ℝ → BoundedContinuousFunction ℂ ℝ) (g : BoundedContinuousFunction ℂ ℝ)
    (hfK : ∀ r, tsupport (f r : ℂ → ℝ) ⊆ K) (hgK : tsupport (g : ℂ → ℝ) ⊆ K)
    (hfg : ∀ δ : ℝ, 0 < δ → ∀ᶠ r : ℝ in atTop, ∀ x, |f r x - g x| ≤ δ) :
    TendstoInMeasure P (fun r ω => regularizedLogChaosTestMass P U dens Y γ r ω (f r)) atTop
      (fun ω => ∫ x, g x ∂N ω) := by
  have hl1 : Tendsto (fun r => ∫⁻ ω, ENNReal.ofReal
      |regularizedLogChaosTestMass P U dens Y γ r ω (f r) -
        regularizedLogChaosTestMass P U dens Y γ r ω g| ∂P) atTop (𝓝 0) := by
    let σ := logRegularizationReference U dens K
    have hσ : σ ≠ ⊤ := admissible_logRegularization_reference_measure_ne_top P U dens ε₀ Y hY K hK hKU
    have hc : ∀ᶠ r : ℝ in atTop, Real.exp (-r) ≤ ε₀ :=
      (eventually_ge_atTop (-Real.log ε₀)).mono fun r hr =>
        (Real.exp_le_exp.2 (by linarith)).trans_eq (Real.exp_log hY.cutoffPositive)
    refine ENNReal.tendsto_atTop_zero.2 fun η hη => ?_
    by_cases hηtop : η = ⊤
    · exact ⟨0, fun _ _ => hηtop ▸ le_top⟩
    let δ := η.toReal / (σ.toReal + 1)
    have hδ : 0 < δ := div_pos (ENNReal.toReal_pos hη.ne' hηtop) (by positivity)
    obtain ⟨R, hR⟩ := eventually_atTop.1 ((hfg δ hδ).and hc)
    refine ⟨R, fun r hr => ?_⟩
    obtain ⟨hδr, hcr⟩ := hR r hr
    have hf0 : ∀ x ∉ K, f r x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hfK r h)
    have hg0 : ∀ x ∉ K, g x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport fun h => hx (hgK h)
    have hfI := admissibleCutoff_integrand_integrable_ae P U dens ε₀ Y hY K hK hKU γ r hcr
      ‖f r‖ (f r) (f r).continuous.measurable (fun x => by simpa [Real.norm_eq_abs] using (f r).norm_coe_le_norm x) hf0
    have hgI := admissibleCutoff_integrand_integrable_ae P U dens ε₀ Y hY K hK hKU γ r hcr
      ‖g‖ g g.continuous.measurable (fun x => by simpa [Real.norm_eq_abs] using g.norm_coe_le_norm x) hg0
    have hb : ∀ᵐ ω ∂P, ENNReal.ofReal |regularizedLogChaosTestMass P U dens Y γ r ω (f r) -
        regularizedLogChaosTestMass P U dens Y γ r ω g| ≤ chartMass P U dens K Y γ r (fun x => |f r x - g x|) ω := by
      filter_upwards [hfI, hgI] with ω hfω hgω
      unfold regularizedLogChaosTestMass
      rw [← integral_sub hfω hgω, show (fun x => f r x * _ - g x * _) =
        fun x => (f r x - g x) * Real.exp (γ * Y ω (Real.exp (-r)) x - γ ^ 2 / 2 * ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P)
        from funext fun _ => by ring]
      have he := enorm_integral_le_lintegral_enorm (μ := logRegularizationReference U dens)
        (fun x => (f r x - g x) * Real.exp (γ * Y ω (Real.exp (-r)) x - γ ^ 2 / 2 * ∫ ω', Y ω' (Real.exp (-r)) x ^ 2 ∂P))
      simp only [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_pos (Real.exp_pos _)] at he
      rwa [lintegral_cutoff_integrand_eq_chartMass P U dens Y K γ r _ (fun _ => abs_nonneg _)
        (fun x hx => by rw [hf0 x hx, hg0 x hx, sub_self, abs_zero]) ω] at he
    refine ((lintegral_mono_ae hb).trans (lintegral_chartMass_le P U dens ε₀ Y hY K γ r hcr δ _
      (continuous_abs.measurable.comp ((f r).continuous.measurable.sub g.continuous.measurable)) hδr)).trans ?_
    change ENNReal.ofReal δ * σ ≤ η
    rw [← ENNReal.ofReal_toReal hσ, ← ENNReal.ofReal_mul hδ.le, ← ENNReal.ofReal_toReal hηtop]
    exact ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hδ.le).trans_eq
      (div_mul_cancel₀ _ (by positivity)))
  let F (r : ℝ) (ω : E) := regularizedLogChaosTestMass P U dens Y γ r ω (f r)
  let G (r : ℝ) (ω : E) := regularizedLogChaosTestMass P U dens Y γ r ω g
  have hz : TendstoInMeasure P (fun r ω => G r ω - F r ω) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_lintegral_ofReal_abs P _ _
      (fun r => ((admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ r g g.continuous.measurable).sub
        (admissibleCutoffIntegral_measurable P U dens ε₀ Y hY γ r (f r) (f r).continuous.measurable)).aestronglyMeasurable)
      aestronglyMeasurable_const (by simpa only [sub_zero, abs_sub_comm] using hl1)
  have heq : (fun r ω => G r ω - (G r ω - F r ω)) = F := by ext; ring
  simpa only [heq, sub_zero] using tendstoInMeasure_sub P G (fun r ω => G r ω - F r ω)
    (fun ω => ∫ x, g x ∂N ω) (fun _ => 0)
    (hN.2.2.2 g (hK.of_isClosed_subset (isClosed_tsupport _) hgK) (hgK.trans hKU)) hz

private lemma cutoffWeightedTest_uniform_approx (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (ρ γ : ℝ) (hρ : 0 < ρ) (hγ : γ ≠ 0) (v : TwoSidedPath)
    (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ))
    (hfU : tsupport (f : ℂ → ℝ) ⊆ originLateralChart ρ) :
    ∀ η : ℝ, 0 < η → ∀ᶠ r : ℝ in atTop, ∀ x,
      |originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ v f hfc x -
        originRadialWeightedTest ρ γ hρ v f hfc x| ≤ η := by
  let K := tsupport (f : ℂ → ℝ)
  let Fexp (r : ℝ) (x : ℂ) := γ * (∫ z, v (clampedLogRadius ρ z) ∂circleMeasure x r) -
    γ ^ 2 / 2 * gaussianVariance P (originCircleRadialL2 hc ρ x r) - 2 * |clampedLogRadius ρ x|
  let Gexp (x : ℂ) := γ * v (clampedLogRadius ρ x) - γ * Q γ * |clampedLogRadius ρ x|
  have hGc : Continuous Gexp :=
    (continuous_const.mul (v.continuous.comp (continuous_clampedLogRadius ρ hρ))).sub
      (continuous_const.mul (continuous_clampedLogRadius ρ hρ).abs)
  have hFG : ∀ η : ℝ, 0 < η → ∀ᶠ r : ℝ in atTop, ∀ x ∈ K, |Fexp r x - Gexp x| < η := fun η hη => by
    let δ := η / (|γ| + |γ ^ 2 / 2| + 1)
    have hden : 0 < |γ| + |γ ^ 2 / 2| + 1 := by positivity
    have hδ : 0 < δ := div_pos hη hden
    obtain ⟨ε₁, hε₁, hrad⟩ := integral_circleMeasure_uniform_approx
      (fun z => v (clampedLogRadius ρ z)) (v.continuous.comp (continuous_clampedLogRadius ρ hρ)) K hfc δ hδ
    obtain ⟨ε₂, hε₂, hvar⟩ := originCircleRadialL2_uniform_variance_approx P X Xc hX hc ρ hρ K hfc hfU δ hδ
    filter_upwards [(tendsto_order.1 Real.tendsto_exp_neg_atTop_nhds_zero).2
      (min ε₁ (min ε₂ ρ)) (lt_min hε₁ (lt_min hε₂ hρ))] with r hr x hx
    have hb₁ : |(∫ z, v (clampedLogRadius ρ z) ∂circleMeasure x r) - v (clampedLogRadius ρ x)| < δ := by
      simpa only [Real.norm_eq_abs] using hrad r (hr.le.trans (min_le_left _ _)) x hx
    have hb₂ := hvar (Real.exp (-r)) (Real.exp_pos _) (hr.le.trans (min_le_right _ _)) x hx
    simp only [one_div, Real.log_inv, Real.log_exp, neg_neg] at hb₂
    have hxρ : ρ ≤ ‖x‖ := by have : 2 * ρ < ‖x‖ := hfU hx; linarith
    have heq : Fexp r x - Gexp x =
        γ * ((∫ z, v (clampedLogRadius ρ z) ∂circleMeasure x r) - v (clampedLogRadius ρ x)) -
        γ ^ 2 / 2 * (gaussianVariance P (originCircleRadialL2 hc ρ x r) - |Real.log ‖x‖|) := by
      dsimp only [Fexp, Gexp]; rw [clampedLogRadius_eq ρ x hxρ, abs_neg, gamma_mul_Q_eq γ hγ]; ring
    rw [heq]
    refine (abs_sub _ _).trans_lt ?_
    rw [abs_mul, abs_mul]
    calc |γ| * _ + |γ ^ 2 / 2| * _ ≤ |γ| * δ + |γ ^ 2 / 2| * δ :=
          add_le_add (mul_le_mul_of_nonneg_left hb₁.le (abs_nonneg _))
            (mul_le_mul_of_nonneg_left hb₂.le (abs_nonneg _))
      _ < (|γ| + |γ ^ 2 / 2| + 1) * δ := by nlinarith
      _ = η := mul_div_cancel₀ _ hden.ne'
  obtain ⟨C, hC⟩ := hfc.bddAbove_image hGc.norm.continuousOn
  let B := |C| + 1
  have huc := isCompact_Icc (a := -B) (b := B) |>.uniformContinuousOn_of_continuous Real.continuous_exp.continuousOn
  intro η hη
  have hηf : 0 < η / (‖f‖ + 1) := div_pos hη (by positivity)
  obtain ⟨δe, hδe, hclose⟩ := Metric.uniformContinuousOn_iff.1 huc (η / (‖f‖ + 1)) hηf
  filter_upwards [hFG (min δe 1) (lt_min hδe zero_lt_one)] with r hr x
  change |f x * Real.exp (Fexp r x) - f x * Real.exp (Gexp x)| ≤ η
  by_cases hx : x ∈ K
  · have hGB : |Gexp x| ≤ |C| := (hC (mem_image_of_mem _ hx)).trans (le_abs_self C)
    have hFB : |Fexp r x| ≤ B := by
      have := abs_add_le (Fexp r x - Gexp x) (Gexp x)
      rw [sub_add_cancel] at this
      have := (hr x hx).le.trans (min_le_right _ _)
      dsimp [B]; linarith
    have hexp : |Real.exp (Fexp r x) - Real.exp (Gexp x)| < η / (‖f‖ + 1) := by
      simpa only [Real.dist_eq] using hclose _ (abs_le.1 hFB) _
        (abs_le.1 (hGB.trans (by dsimp [B]; linarith)))
        (by simpa only [Real.dist_eq] using (hr x hx).trans_le (min_le_left _ _))
    rw [← mul_sub, abs_mul]
    calc |f x| * _ ≤ ‖f‖ * (η / (‖f‖ + 1)) := mul_le_mul
            (by simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x) hexp.le (abs_nonneg _) (norm_nonneg _)
      _ ≤ (‖f‖ + 1) * (η / (‖f‖ + 1)) := mul_le_mul_of_nonneg_right (by linarith) hηf.le
      _ = η := mul_div_cancel₀ _ (by positivity)
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul, sub_self, abs_zero]; exact hη.le

/-- The actual local lateral chaos admits the finite radial cutoff-weighted limit on the
original field space, while remaining independent of the whole radial path. -/
theorem exists_originLateralChartGMC_cutoff_weighted_limit (P : Measure Ω)
    (X : Ω → Distr) (Xc : Ω → ℂ → ℝ → ℝ)
    (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (ρ : ℝ) (hρ : 0 < ρ) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ N : Ω → Measure ℂ,
      IsAdmissibleGMCVersion P (originLateralChart ρ) originLateralPlaneDensity
        (originLateralCircleRegularization Xc ρ) γ N ∧
      IndepFun (originRadialPath Xc) N P ∧
      ∀ (f : BoundedContinuousFunction ℂ ℝ) (hfc : HasCompactSupport (f : ℂ → ℝ)),
        tsupport (f : ℂ → ℝ) ⊆ originLateralChart ρ →
        TendstoInMeasure P
          (fun r ω => regularizedLogChaosTestMass P (originLateralChart ρ)
            originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ r ω
              (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (originRadialPath Xc ω) f hfc)) atTop
          (fun ω => ∫ x, originRadialWeightedTest ρ γ hρ (originRadialPath Xc ω) f hfc x ∂N ω) := by
  let _ := hX.1
  have hpath := originLateralCutoffPath_aemeasurable P Xc hm hcont ρ hρ
  let π := hpath.mk (originLateralCutoffPath Xc ρ)
  have hπm := hpath.measurable_mk
  have hπ := hpath.ae_eq_mk.symm
  have hAm := originRadialPath_aemeasurable P X Xc hc hcont
  let A := hAm.mk (originRadialPath Xc)
  have hAm' := hAm.measurable_mk
  have hA : A =ᵐ[P] originRadialPath Xc := hAm.ae_eq_mk.symm
  have hi := (originRadialPath_lateralCutoffPath_indepFun P X Xc hX hc hm hcont ρ hρ).congr
    hAm.ae_eq_mk hpath.ae_eq_mk
  have hY := originLateralUniversalRegularization_admissible P X Xc hX hc hm hcont ρ hρ π hπm hπ
  obtain ⟨N, hN⟩ := admissibleLogRegularization_GMC_exists (P.map π)
    (originLateralChart ρ) originLateralPlaneDensity (Real.exp (-originLateralCutoffBaseTime ρ))
    (originLateralUniversalRegularization ρ hρ) hY γ hγ hγ2
  have hcomp := originLateralUniversalRegularization_comp_ae P Xc hcont ρ hρ π hπ
  refine ⟨fun ω => N (π ω),
    isAdmissibleGMCVersion_map_pullback P π hπm (originLateralChart ρ)
      (isOpen_originLateralChart ρ) originLateralPlaneDensity _ (Real.exp_pos _)
      (originLateralCircleRegularization Xc ρ) (originLateralUniversalRegularization ρ hρ)
      (originLateralUniversalRegularization_measurableAtScale ρ hρ) hcomp γ N hN,
    (hi.congr hA EventuallyEq.rfl).comp measurable_id hN.1, fun f hfc hfU => ?_⟩
  let E := C(OriginLateralCutoffDomain ρ, ℝ)
  let Fm (r : ℝ) (v : TwoSidedPath) (ξ : E) :=
    regularizedLogChaosTestMass (P.map π) (originLateralChart ρ) originLateralPlaneDensity
      (originLateralUniversalRegularization ρ hρ) γ r ξ (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ v f hfc)
  let Gm (v : TwoSidedPath) (ξ : E) := ∫ x, originRadialWeightedTest ρ γ hρ v f hfc x ∂N ξ
  have hmF (r : ℝ) : Measurable (Function.uncurry (Fm r)) := by
    let Y := originLateralUniversalRegularization ρ hρ
    have hv : Measurable (fun x : ℂ => ∫ ξ, Y ξ (Real.exp (-r)) x ^ 2 ∂P.map π) :=
      ((hY.measurableAtScale _).comp measurable_swap).pow_const 2 |>.stronglyMeasurable.integral_prod_right.measurable
    have hw := (continuous_originRadialCutoffReinsertionWeight_joint P X Xc hX hc ρ γ hρ).measurable.comp
      (measurable_fst.prodMk (measurable_snd.prodMk (measurable_const : Measurable fun _ => r)))
    have htest : Measurable (fun p : (TwoSidedPath × E) × ℂ =>
        originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ p.1.1 f hfc p.2) :=
      ((f.continuous.measurable.comp measurable_snd).mul hw).comp (measurable_fst.fst.prodMk measurable_snd)
    have hfield : Measurable (fun p : (TwoSidedPath × E) × ℂ => Y p.1.2 (Real.exp (-r)) p.2) :=
      (hY.measurableAtScale _).comp (measurable_fst.snd.prodMk measurable_snd)
    exact (htest.mul ((hfield.const_mul γ).sub
      ((hv.comp measurable_snd).const_mul (γ ^ 2 / 2))).exp).stronglyMeasurable.integral_prod_right.measurable
  have hmG := originRadialWeightedTest_integral_measurable ρ γ hρ f hfc N hN.1 fun ξ => hN.2.2.1 ξ _ hfc hfU
  have ht := tendstoInMeasure_independent_parameters P A π hAm' hπm hi Fm Gm hmF hmG fun v =>
    varying_test_tendstoInMeasure (P.map π) (originLateralChart ρ) originLateralPlaneDensity _
      (originLateralUniversalRegularization ρ hρ) hY γ N hN (tsupport (f : ℂ → ℝ)) hfc hfU
      (fun r => originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ v f hfc)
      (originRadialWeightedTest ρ γ hρ v f hfc)
      (fun _ => tsupport_mul_subset_left)
      (tsupport_originRadialWeightedTest_subset ρ γ hρ v f hfc)
      (cutoffWeightedTest_uniform_approx P X Xc hX hc ρ γ hρ hγ.ne' v f hfc hfU)
  have hleft : ∀ᶠ r : ℝ in atTop,
      (fun ω => Fm r (A ω) (π ω)) =ᵐ[P] fun ω => regularizedLogChaosTestMass P (originLateralChart ρ)
        originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ r ω
        (originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (originRadialPath Xc ω) f hfc) := by
    filter_upwards [eventually_ge_atTop (originLateralCutoffBaseTime ρ)] with r hr
    have heq := regularizedLogChaosTestMass_randomTest_map_comp P π hπm
      (originLateralChart ρ) (isOpen_originLateralChart ρ) originLateralPlaneDensity
      (originLateralCircleRegularization Xc ρ) (originLateralUniversalRegularization ρ hρ)
      (originLateralUniversalRegularization_measurableAtScale ρ hρ) γ r
      (fun ω => originRadialCutoffWeightedTest P X Xc hX hc ρ γ r hρ (A ω) f hfc)
      (hcomp.mono fun ω hω => hω _ (Real.exp_pos _) (Real.exp_le_exp.2 (neg_le_neg hr)))
    filter_upwards [heq, hA] with ω hω hAω; dsimp [Fm] at *; rw [hω, hAω]
  exact TendstoInMeasure.congr' hleft (hA.mono fun ω hω => by dsimp [Gm]; rw [hω]) ht

end DOZZ.Proofs
