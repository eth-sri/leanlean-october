module
public import NearlyMinimax.PathRisk
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import NearlyMinimax.Clipping
@[expose] public section
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
theorem absolutelyContinuous_path_separation_le {m score : ℝ → ℝ} {δ r V₀ Vδ : ℝ}
    (hδ : 0 ≤ δ) (hAC : AbsolutelyContinuousOnInterval m 0 δ)
    (hscore : IntervalIntegrable score volume 0 δ)
    (hbound : ∀ᵐ t ∂volume, t ∈ Icc 0 δ → |deriv m t| ≤ r * score t)
    (hfirst : |m 0 - V₀| ≤ r) (hlast : |m δ - Vδ| ≤ r) :
    |Vδ - V₀| ≤ (2 + ∫ t in 0..δ, score t) * r := by
  have h_absolutelyContinuous_path_mean_change_le : |m δ - m 0| ≤ r * ∫ t in 0..δ, score t := by
    rw [← hAC.integral_deriv_eq_sub, ← intervalIntegral.integral_const_mul]
    apply (show ‖∫ t in 0..δ, deriv m t‖ ≤ _ from
      intervalIntegral.norm_integral_le_of_norm_le hδ ?_ (hscore.const_mul r))
    filter_upwards [hbound] with t ht hmem
    exact ht ⟨hmem.1.le, hmem.2⟩
  have hchange := h_absolutelyContinuous_path_mean_change_le
  calc
    |Vδ - V₀| = |(Vδ - m δ) + (m δ - m 0) + (m 0 - V₀)| := by congr 1; ring
    _ ≤ |Vδ - m δ| + |m δ - m 0| + |m 0 - V₀| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ r + (r * ∫ t in 0..δ, score t) + r := by
      rw [abs_sub_comm Vδ (m δ)]
      exact add_le_add (add_le_add hlast hchange) hfirst
    _ = _ := by ring
theorem probability_kernel_integral  [MeasurableSpace Α] [MeasurableSpace Ω]
    (μ : Measure Α) [IsProbabilityMeasure μ] (K : Kernel Α Ω) [IsMarkovKernel K]
    (f : Ω → ℝ) (hf : Integrable f (K ∘ₘ μ)) :
    (∫ x, f x ∂(K ∘ₘ μ)) = ∫ a, ∫ x, f x ∂K a ∂μ := by
  have h := Kernel.integral_comp (κ := Kernel.const Unit μ) (η := K) (a := ())
    (f := f) (by simpa only [← Measure.comp_eq_comp_const_apply] using hf)
  simpa only [Kernel.const_apply, ← Measure.comp_eq_comp_const_apply] using h
theorem boundedEstimator_worstCaseRisk_finite  (C : ModelConstants d)
    (T : BoundedEstimator C n) : worstCaseRisk C T.val < ∞ := by
  have hb : worstCaseRisk C T.val ≤
      ENNReal.ofReal ((effectiveVarianceUpper C - C.varianceLower) ^ 2) :=
    iSup_le (fun θ => boundedEstimator_risk_le_diameter C T θ.val θ.property)
  exact hb.trans_lt ENNReal.ofReal_lt_top
theorem boundedEstimator_mixture_risk_le_of_exceptional_set  [MeasurableSpace Α]
     (C : ModelConstants d) (T : BoundedEstimator C n)
    (σ : Measure Α) [IsProbabilityMeasure σ]
    (L : Kernel Α (Fin n → Observation d)) [IsMarkovKernel L]
    (θ : Α → RegressionParameter d) (V ε : ℝ)
    (hL : ∀ a, L a = sampleLaw (θ a) n) (hVθ : ∀ a, (θ a).variance = V)
    (hV : V ∈ Icc C.varianceLower (effectiveVarianceUpper C))
    (bad : Set Α) (hbad : MeasurableSet bad)
    (hlegal : ∀ a ∉ bad, Admissible C (θ a))
    (hmass : σ.real bad ≤ ε) :
    (∫ x, (T.val.val x - V) ^ 2 ∂(L ∘ₘ σ)) ≤
      (worstCaseRisk C T.val).toReal + (effectiveVarianceUpper C - C.varianceLower) ^ 2 * ε := by
  let D := effectiveVarianceUpper C - C.varianceLower
  let f (x : Fin n → Observation d) := (T.val.val x - V) ^ 2
  have hfmeas := (T.val.property.sub_const V).pow_const ↑2
  have hf0 (x : Fin n → Observation d) : 0 ≤ f x := sq_nonneg _
  have hcap (x : Fin n → Observation d) : f x ≤ D ^ 2 := by
    have ht := T.property x
    have hD : 0 ≤ D := sub_nonneg.mpr (effective_variance_interval_nondegenerate C).le
    simpa only [f, sq_abs] using (sq_le_sq₀ (abs_nonneg _) hD).mpr (by apply abs_le.mpr; constructor <;> dsimp only [D] <;> linarith only [ht.1, ht.2, hV.1, hV.2])
  have hfi (μ : Measure (Fin n → Observation d)) [IsProbabilityMeasure μ] : Integrable f μ := by
    apply (integrable_const (D ^ 2)).mono' hfmeas.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hcap x
  let e (a : Α) := ∫ x, f x ∂L a
  have he0 (a : Α) : 0 ≤ e a := integral_nonneg hf0
  have hecap (a : Α) : e a ≤ D ^ 2 := by
    have h := integral_mono (hfi (L a)) (integrable_const (D ^ 2)) hcap
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hei : Integrable e σ := by
    apply (integrable_const (D ^ 2)).mono' (hfmeas.stronglyMeasurable.integral_kernel.measurable).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (he0 a)]
      exact hecap a
  have hgood (a : Α) (ha : Admissible C (θ a)) : e a ≤ (worstCaseRisk C T.val).toReal := by
    have heq : ENNReal.ofReal (e a) = meanSquaredRisk T.val (θ a) := by
      rw [meanSquaredRisk, ← hL a, hVθ a]
      exact ofReal_integral_eq_lintegral_ofReal (hfi (L a))
        (Filter.Eventually.of_forall hf0)
    have h := ENNReal.toReal_mono (boundedEstimator_worstCaseRisk_finite C T).ne
      (meanSquaredRisk_le_worstCaseRisk C T.val (θ a) ha)
    rwa [← heq, ENNReal.toReal_ofReal (he0 a)] at h
  rw [probability_kernel_integral σ L f (hfi (L ∘ₘ σ))]
  exact probability_mixture_exceptional_risk_bound σ e bad hbad
    (worstCaseRisk C T.val).toReal D ε hei ENNReal.toReal_nonneg
    (Filter.Eventually.of_forall (fun a ha => hgood a (hlegal a ha)))
    (Filter.Eventually.of_forall (fun a _ => hecap a)) hmass
end NearlyMinimax
