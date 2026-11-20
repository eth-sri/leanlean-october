module

public import NearlyMinimax.AbsolutelyContinuousPathRisk
public import NearlyMinimax.Clipping

@[expose] public section

/-! Exceptional-state risk control for actual probability mixtures of original
sample laws. Clipping and the exceptional contribution are both derived. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

variable {Α Ω : Type*}

theorem probability_kernel_integral [MeasurableSpace Α] [MeasurableSpace Ω]
    {μ : Measure Α} [IsProbabilityMeasure μ] {K : Kernel Α Ω} [IsMarkovKernel K]
    {f : Ω → ℝ} (hf : Integrable f (K ∘ₘ μ)) :
    (∫ x, f x ∂(K ∘ₘ μ)) = ∫ a, ∫ x, f x ∂K a ∂μ := by
  have h := Kernel.integral_comp (κ := Kernel.const Unit μ) (a := ()) (by assumption)
  assumption

theorem boundedEstimator_worstCaseRisk_finite {d n : ℕ} {C : ModelConstants d}
    (T : BoundedEstimator C n) : worstCaseRisk C T.val < ∞ := (iSup_le (fun θ => boundedEstimator_risk_le_diameter T θ.property)).trans_lt ENNReal.ofReal_lt_top

theorem boundedEstimator_mixture_risk_le_of_exceptional_set [MeasurableSpace Α]
    {d n : ℕ} {C : ModelConstants d} (T : BoundedEstimator C n)
    {σ : Measure Α} [IsProbabilityMeasure σ]
    {L : Kernel Α (Fin n → Observation d)} [IsMarkovKernel L]
    {θ : Α → RegressionParameter d} {V ε : ℝ}
    (hL : ∀ a, L a = sampleLaw (θ a) n) (hVθ : ∀ a, (θ a).variance = V)
    (hV : V ∈ Icc C.varianceLower (effectiveVarianceUpper C))
    {bad : Set Α} (hbad : MeasurableSet bad)
    (hlegal : ∀ a ∉ bad, Admissible C (θ a))
    (hmass : σ.real bad ≤ ε) :
    (∫ x, (T.val.val x - V) ^ 2 ∂(L ∘ₘ σ)) ≤
      (worstCaseRisk C T.val).toReal + (effectiveVarianceUpper C - C.varianceLower) ^ 2 * ε := by
  let D := effectiveVarianceUpper C - C.varianceLower
  let f x := (T.val.val x - V) ^ 2
  have hfmeas  := (T.val.property.sub_const V).pow_const 2
  have hf0 x : 0 ≤ f x := sq_nonneg _
  have hcap x : f x ≤ D ^ 2 := by
    have hD : 0 ≤ D := sub_nonneg.mpr (effective_variance_interval_nondegenerate C).le
    simpa using (sq_le_sq₀ (abs_nonneg _) hD).mpr (by
      grind)
  have hfi (μ : Measure (Fin n → Observation d)) [IsProbabilityMeasure μ] : Integrable f μ := by
    apply (integrable_const (D ^ 2)).mono' hfmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hcap x
  let e a := ∫ x, f x ∂L a
  have he0 a : 0 ≤ e a := integral_nonneg hf0
  have hecap a : e a ≤ D ^ 2 := by
    have h := integral_mono (hfi (L a)) (integrable_const (D ^ 2)) hcap
    simpa using h
  have hei : Integrable e σ := by
    apply (integrable_const (D ^ 2)).mono' hfmeas.stronglyMeasurable.integral_kernel.measurable.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (he0 a)]
      exact hecap a
  have hgood a (ha : Admissible C (θ a)) : e a ≤ (worstCaseRisk C T.val).toReal := by
    have heq : ENNReal.ofReal (e a) = meanSquaredRisk T.val (θ a) := by
      rw [meanSquaredRisk, ← hL a, hVθ a]
      exact ofReal_integral_eq_lintegral_ofReal (hfi (L a))
        (Filter.Eventually.of_forall hf0)
    have h := ENNReal.toReal_mono (boundedEstimator_worstCaseRisk_finite T).ne
      (meanSquaredRisk_le_worstCaseRisk C T.val _ ha)
    rwa [← heq, ENNReal.toReal_ofReal (he0 a)] at h
  rw [probability_kernel_integral (hfi (L ∘ₘ σ))]
  exact probability_mixture_exceptional_risk_bound hbad hei ENNReal.toReal_nonneg
    (Filter.Eventually.of_forall (fun a ha => by bound))
    (Filter.Eventually.of_forall (fun a _ => hecap a)) hmass

end NearlyMinimax
