module

public import NearlyMinimax.LowMixtureLaw
public import NearlyMinimax.LowMixtureProbability
public import NearlyMinimax.GridMixtureDerivative
public import Mathlib.Analysis.Calculus.MeanValue


@[expose] public section

/-! Genuine original-model prior risk and centered score bounds for the grid experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem gridSampleField_coordinate_measurable (d k n : ℕ) (η : ℝ)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) :
    Measurable (fun x => gridSampleField d k n η x ξ i) :=
  (measurable_pi_apply i).comp ((measurable_pi_apply ξ).comp
    (gridSampleField_measurable d k n η))

def gridMixtureLaw (d k n : ℕ) (a v η t : ℝ) :
    Measure ((Fin n → Covariate d) × LowMixtureMarks (gridWindowCount d k) n) :=
  lowMixtureLaw (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n
    a (v - η ^ 2 * t) t (gridSampleField d k n η)
    (gridSampleField_coordinate_measurable d k n η)

def gridMixtureScore (d k n : ℕ) (a v η t : ℝ) :
    (Fin n → Covariate d) × LowMixtureMarks (gridWindowCount d k) n → ℝ :=
  lowMixtureScore (gridWindowCount d k) n a (v - η ^ 2 * t) η (gridSampleField d k n η)

def gridLiftedObservable {d n : ℕ} (k : ℕ) (a : ℝ) (T : Estimator d n) :
    (Fin n → Covariate d) × LowMixtureMarks (gridWindowCount d k) n → ℝ :=
  fun z => T.val (encodeDesignResponse a (z.1, z.2.2))

theorem gridLiftedObservable_measurable {d n : ℕ} (k : ℕ) (a : ℝ)
    (T : Estimator d n) : Measurable (gridLiftedObservable k a T) :=
  (T.property.comp (encodeDesignResponse_measurable a)).comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

theorem gridSampleField_eq_latent (d k n : ℕ) (η : ℝ) (x : Fin n → Covariate d) :
    gridSampleField d k n η x =
      latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) := by
  funext ξ i
  exact (grid_latent_regression_eq d k n η x ξ i).symm

section
variable {d : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1)
include hamp ht

private theorem gridStateEnergy_integrable (ξ : Fin (gridWindowCount d k) → Fin 3) :
    Integrable (fun x => ∑ y,
      finiteResponseLikelihood (gridWindowCount d k) n P.a (P.v - η^2*t) (gridSampleField d k n η x) ξ y *
      finiteExperimentScore (gridWindowCount d k) n P.a (P.v - η^2*t) η (gridSampleField d k n η x) ξ y ^ 2)
      (Measure.pi (fun _ : Fin n => cubeVolume d)) := by
  exact (grid_full_score_energy_integrable C P k n η t ξ hamp ht).congr
    (.of_forall fun x => by simp only [gridFullScoreEnergy,
      LowSmoothnessTernaryConstants.variancePath, gridSampleField_eq_latent])

theorem grid_mixture_probability :
    IsProbabilityMeasure (gridMixtureLaw d k n P.a P.v η t) := by
  let _ := cubeVolume_isProbability d
  exact lowMixtureLaw_probability _ _ _ _ _ _ _ _ P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive C P k n η t ξ x hamp ht i y).le)

private theorem grid_mixture_score_facts :
    let μ := gridMixtureLaw d k n P.a P.v η t
    let S := gridMixtureScore d k n P.a P.v η t
    MemLp S 2 μ ∧ (∫ z, S z ∂μ) = 0 ∧ (∫ z, S z ^ 2 ∂μ) = gridPriorScoreEnergy d k n P.a P.v η t := by
  let _ := cubeVolume_isProbability d
  simpa only [gridMixtureScore, gridMixtureLaw, lowResponseMean, lowMixtureScore, gridPriorScoreEnergy,
    gridFullScoreEnergy, LowSmoothnessTernaryConstants.variancePath, gridSampleField_eq_latent] using
    lowMixtureScore_facts (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n
      P.a (P.v - η ^ 2 * t) η t (gridSampleField d k n η)
      (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
      (fun x ξ i y => grid_response_positive C P k n η t ξ x hamp ht i y)
      (gridStateEnergy_integrable C P k n η t hamp ht)

theorem gridMixtureLaw_integral
    (H : (Fin n → Covariate d) × LowMixtureMarks (gridWindowCount d k) n → ℝ)
    (hH : Integrable H (gridMixtureLaw d k n P.a P.v η t)) :
    (∫ z, H z ∂gridMixtureLaw d k n P.a P.v η t) =
      ∫ x, ∑ ξ, activationProductPrior (gridWindowCount d k) t ξ *
        ∑ y, finiteResponseLikelihood (gridWindowCount d k) n P.a (P.v-η^2*t)
          (gridSampleField d k n η x) ξ y * H (x,ξ,y) ∂Measure.pi (fun _ : Fin n => cubeVolume d) := by
  let := cubeVolume_isProbability d
  exact lowMixtureLaw_integral _ _ _ _ _ _ _ _ P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive C P k n η t ξ x hamp ht i y).le) _ hH

end

theorem grid_lifted_observable_memLp {d n : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η t : ℝ)
    (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1)
    (T : BoundedEstimator C n) :
    MemLp (gridLiftedObservable k P.a T.val) 2 (gridMixtureLaw d k n P.a P.v η t) := by
  let := grid_mixture_probability C P k n η t hamp ht
  exact MemLp.of_bound (gridLiftedObservable_measurable k P.a T.val).aestronglyMeasurable
    (effectiveVarianceUpper C) (.of_forall fun z => (Real.norm_eq_abs _).trans_le (T.abs_le C _))

section
variable {d n : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ)

theorem grid_mixture_risk_le_original_worstCase (η b t : ℝ)
    (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b)
    (hamp : GridAmplitudeBounds d η P.ρ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : gridHolderBudget d * b ≤ C.holderBound)
    (T : BoundedEstimator C n) :
    (∫ z, (gridLiftedObservable k P.a T.val z - (P.v - η ^ 2 * t)) ^ 2
      ∂gridMixtureLaw d k n P.a P.v η t) ≤ (worstCaseRisk C T.val).toReal := by
  let _ := cubeVolume_isProbability d
  have hξ (ξ : Fin (gridWindowCount d k) → Fin 3) :=
    gridPathParameter_risk_formula C P k η t ξ hamp ht T
  unfold gridMixtureLaw
  rw [(lowMixtureLaw_nonneg_moments
    (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n
    P.a (P.v - η ^ 2 * t) t (gridSampleField d k n η)
    (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive C P k n η t ξ x hamp ht i y).le)
    _ ((gridLiftedObservable_measurable k P.a T.val).sub_const _ |>.pow_const 2)
    (fun _ => sq_nonneg _) (fun ξ => (hξ ξ).1)).2]
  calc
    _ ≤ ∑ ξ : Fin (gridWindowCount d k) → Fin 3,
      activationProductPrior (gridWindowCount d k) t ξ * (worstCaseRisk C T.val).toReal := by
      apply Finset.sum_le_sum
      intro ξ _
      apply mul_le_mul_of_nonneg_left
      · apply (ENNReal.ofReal_le_iff_le_toReal (boundedEstimator_worstCaseRisk_ne_top C T)).mp
        change ENNReal.ofReal (∫ x, gridStateRisk k P.a P.v η t T.val ξ x
          ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤ _
        rw [(hξ ξ).2]
        exact le_iSup (fun θ : {θ // Admissible C θ} => meanSquaredRisk T.val θ.val)
          ⟨_, gridPathParameter_admissible C P k η b t ξ hk hs1 hb hamp ht hscale hholder⟩
      · exact Finset.prod_nonneg (fun j _ => activation_prior_nonnegative t ht.1 ht.2 (ξ j))
    _ = _ := by rw [← Finset.sum_mul, activation_product_prior_normalized, one_mul]

end

def gridEncodedObservable {d n : ℕ} (a : ℝ) (T : Estimator d n) :
    (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ :=
  fun x y => T.val (encodeDesignResponse a (x, y))

section
variable {d n : ℕ}

theorem gridEncodedObservable_measurable (a : ℝ) (T : Estimator d n) :
    Measurable (gridEncodedObservable a T) := by
  apply Measurable.of_eval
  intro y
  exact (T.property.comp (encodeDesignResponse_measurable a)).comp
    (measurable_id.prodMk measurable_const)

section
variable (C : ModelConstants d)

theorem gridEncodedObservable_norm_le
    (a : ℝ) (T : BoundedEstimator C n) (x : Fin n → Covariate d) :
    ‖gridEncodedObservable a T.val x‖ ≤ effectiveVarianceUpper C := by
  have hC :=
    C.varianceLower_pos.le.trans (effective_variance_interval_nondegenerate C).le
  apply (pi_norm_le_iff_of_nonneg hC).mpr
  exact fun y => (Real.norm_eq_abs _).trans_le (T.abs_le C _)

/-- The complete actual-model score argument. All latent states obey the
original Hölder/moment class and all score and risk identities are derived. -/
theorem grid_prior_boundedEstimator_separation
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η b : ℝ)
    (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b) (hamp : GridAmplitudeBounds d η P.ρ)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : gridHolderBudget d * b ≤ C.holderBound)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) (hbudget : gridUniformScoreBudget P k n η ≤ 1)
    (T : BoundedEstimator C n) :
    η ^ 2 ≤ 3 * Real.sqrt ((worstCaseRisk C T.val).toReal) := by
  let r := Real.sqrt ((worstCaseRisk C T.val).toReal)
  let m := fun t => gridMixtureExpectation d k n P.a P.v η t (gridEncodedObservable P.a T.val)
  let m' := fun t => ∫ x,
    gridMixtureScoreObservable d k n P.a P.v η t (gridEncodedObservable P.a T.val) x
    ∂Measure.pi (fun _ : Fin n => cubeVolume d)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (worstCaseRisk C T.val).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hT := gridEncodedObservable_measurable P.a T.val
  have hTB : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => cubeVolume d),
      ‖gridEncodedObservable P.a T.val x‖ ≤ effectiveVarianceUpper C :=
    Filter.Eventually.of_forall (gridEncodedObservable_norm_le C P.a T)
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :=
    grid_mixture_expectation_hasDerivAt C P k n η t (effectiveVarianceUpper C) hamp ht _ hT hTB
  have hbounds (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      |m t - (P.v - η ^ 2 * t)| ≤ r ∧ ‖m' t‖ ≤ r := by
    let _ := grid_mixture_probability C P k n η t hamp ht
    obtain ⟨hR, hc, he⟩ := grid_mixture_score_facts C P k n η t hamp ht
    have hL := grid_lifted_observable_memLp C P k η t hamp ht T
    have hris := grid_mixture_risk_le_original_worstCase C P k η b t hk hs1 hb hamp ht hscale hholder T
    rw [← hr2] at hris
    have hm := probability_mean_error_le _ _ _ _ hL hr hris
    rw [gridMixtureLaw_integral C P k n η t hamp ht _ (hL.integrable (by norm_num))] at hm
    refine ⟨hm, ?_⟩
    have hD := probability_score_bound _ _ _ _ r hL hR hr hc hris
    have hI := gridMixtureLaw_integral C P k n η t hamp ht _ (hL.integrable_mul hR)
    simp only [Pi.mul_apply] at hI
    rw [hI, he] at hD
    have hscore := Real.sqrt_le_sqrt ((grid_prior_score_energy_bound C P k n η t hk hamp ht hmean).trans hbudget)
    rw [Real.sqrt_one] at hscore
    simpa only [m', Real.norm_eq_abs, gridLiftedObservable, gridMixtureScore, gridMixtureScoreObservable,
      gridEncodedObservable, lowMixtureScore, lowMixtureMean, lowResponseMean, Pi.mul_apply, mul_assoc, mul_one] using
      hD.trans (mul_le_mul_of_nonneg_left hscore hr)
  have h0 : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  have hmove : |m 1 - m 0| ≤ r := by
    simpa [Real.norm_eq_abs] using (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hderiv t ht).hasDerivWithinAt) (fun t ht => (hbounds t ht).2) h0 h1
  have hsep := endpoint_separation_le (hbounds 0 h0).1 (hbounds 1 h1).1 hmove
  simp at hsep
  linarith only [hsep]

/-- Actual minimax RMS lower bound from the fully constructed grid prior. -/
theorem grid_prior_minimax_lower
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η b : ℝ)
    (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b) (hamp : GridAmplitudeBounds d η P.ρ)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : gridHolderBudget d * b ≤ C.holderBound)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) (hbudget : gridUniformScoreBudget P k n η ≤ 1) :
    ENNReal.ofReal (η ^ 2 / 3) ≤ minimaxRMS C n := by
  have hnonneg : 0 ≤ η ^ 2 / 3 := by positivity
  have hlower : ENNReal.ofReal (η ^ 2 / 3) ^ 2 ≤ minimaxRisk C n := by
    rw [minimaxRisk_eq_inf_bounded C n]
    apply le_iInf
    intro T
    rw [← ENNReal.ofReal_pow hnonneg 2]
    apply (ENNReal.ofReal_le_iff_le_toReal (boundedEstimator_worstCaseRisk_ne_top C T)).mpr
    have hsep := grid_prior_boundedEstimator_separation C P k η b hk hs1 hb hamp hscale hholder hmean hbudget T
    have hdiv : η ^ 2 / 3 ≤ Real.sqrt ((worstCaseRisk C T.val).toReal) := by linarith
    have hsq := pow_le_pow_left₀ hnonneg hdiv 2
    rwa [Real.sq_sqrt ENNReal.toReal_nonneg] at hsq
  have h := ENNReal.rpow_le_rpow hlower (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have he : (ENNReal.ofReal (η ^ 2 / 3) ^ 2) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (η ^ 2 / 3) := by
    rw [← ENNReal.rpow_natCast_mul]
    norm_num
  rw [he] at h
  exact h

end

end

end NearlyMinimax
