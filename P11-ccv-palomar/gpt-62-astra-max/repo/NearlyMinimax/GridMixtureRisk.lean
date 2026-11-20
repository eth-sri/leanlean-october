module

public import NearlyMinimax.LowMixtureLaw
public import NearlyMinimax.LowMixtureProbability
public import NearlyMinimax.GridMixtureDerivative
public import NearlyMinimax.GridScorePath


@[expose] public section

/-! Genuine original-model prior risk and centered score bounds for the grid experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace NearlyMinimax

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

section
variable (d k n : ℕ) (a v η t : ℝ)

theorem gridSampleField_coordinate_measurable
    (ξ : TernaryVector (gridWindowCount d k)) (i : Fin n) :
    Measurable (fun x => gridSampleField d k n η x ξ i) :=
  (measurable_pi_apply i).comp ((measurable_pi_apply ξ).comp
    (gridSampleField_measurable ..))

def gridMixtureLaw :
    Measure ((DesignSample d n) × LowMixtureMarks (gridWindowCount d k) n) :=
  lowMixtureLaw (Measure.pi (fun _ => cubeVolume d))
    a (v - η ^ 2 * t) t
    (gridSampleField_coordinate_measurable d k n η)

def gridMixtureScore :
    (DesignSample d n) × LowMixtureMarks (gridWindowCount d k) n → ℝ :=
  lowMixtureScore a (v - η ^ 2 * t) η (gridSampleField d k n η)

end

section
variable {d n : ℕ} (k : ℕ) (a : ℝ) (T : Estimator d n)

def gridLiftedObservable :
    (DesignSample d n) × LowMixtureMarks (gridWindowCount d k) n → ℝ :=
  fun z => T.val (encodeDesignResponse a (z.1, z.2.2))

theorem gridLiftedObservable_measurable : Measurable (gridLiftedObservable k a T) :=
  (T.property.comp (encodeDesignResponse_measurable a)).comp
    (by fun_prop)

end

theorem gridSampleField_eq_latent (d k n : ℕ) (η : ℝ) (x : DesignSample d n) :
    gridSampleField d k n η x =
      latentRegression η (fun _ => 0) (gridSampleWeights k x) := by
  funext ξ i
  exact (grid_latent_regression_eq η x ξ i).symm

section
variable {d : ℕ} {C : ModelConstants d} {P : LowSmoothnessTernaryConstants C} (k n : ℕ) {η t : ℝ}
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ)
    (hvariance : η ^ 2 ≤ P.ρ)
include hfield ht hvariance hη

theorem gridMixtureConditionalEnergy_integrable :
    Integrable (lowMixtureConditionalScoreEnergy P.a
      (P.v - η ^ 2 * t) η t (gridSampleField d k n η))
      (Measure.pi (fun _ => cubeVolume d)) := by
  unfold lowMixtureConditionalScoreEnergy
  have hξ ξ :=
    ((grid_full_score_energy_control k n ξ hη ht hfield hvariance).1).const_mul
      (activationProductPrior t ξ)
  simpa only [gridFullScoreEnergy,
    LowSmoothnessTernaryConstants.variancePath, gridSampleField_eq_latent] using
    integrable_finsetSum Finset.univ (fun ξ _ => hξ ξ)

theorem grid_mixture_probability :
    IsProbabilityMeasure (gridMixtureLaw d k n P.a P.v η t) := by
  let _ := cubeVolume_isProbability d
  exact lowMixtureLaw_probability _ _ _ _ _ _ _ _ P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive ξ x hη ht hfield hvariance i y).le)

theorem grid_mixture_score_memLp :
    MemLp (gridMixtureScore d k n P.a P.v η t) 2
      (gridMixtureLaw d k n P.a P.v η t) := by
  let _ := cubeVolume_isProbability d
  exact lowMixtureScore_memLp_two _ P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive ξ x hη ht hfield hvariance i y).le)
    (gridMixtureConditionalEnergy_integrable k n hη ht hfield hvariance)

theorem grid_mixture_score_centered :
    (∫ z, gridMixtureScore d k n P.a P.v η t z
      ∂gridMixtureLaw d k n P.a P.v η t) = 0 := by
  let _ := cubeVolume_isProbability d
  exact lowMixtureScore_centered _ P.a_pos.ne' ht
    (fun x ξ i y => grid_response_positive ξ x hη ht hfield hvariance i y)
    (gridMixtureConditionalEnergy_integrable k n hη ht hfield hvariance)

theorem grid_mixture_score_energy :
    (∫ z, (gridMixtureScore d k n P.a P.v η t z) ^ 2
      ∂gridMixtureLaw d k n P.a P.v η t) = gridPriorScoreEnergy d k n P.a P.v η t := by
  let _ := cubeVolume_isProbability d
  have hξ ξ :=
    (grid_full_score_energy_control k n ξ hη ht hfield hvariance).1
  simpa only [gridMixtureScore, gridMixtureLaw, gridPriorScoreEnergy,
    gridFullScoreEnergy, 
    gridSampleField_eq_latent] using lowMixtureScore_sq_integral_eq_sum
      (Measure.pi (fun _ => cubeVolume d))
      P.a (P.v - η ^ 2 * t) η t
      (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
      (fun x ξ i y => (grid_response_positive ξ x hη ht hfield hvariance i y).le)
      (fun ξ => (hξ ξ).congr (Filter.Eventually.of_forall (fun x => by
        simp only [gridFullScoreEnergy, LowSmoothnessTernaryConstants.variancePath,
          gridSampleField_eq_latent])))

end

section
variable {d n : ℕ} {C : ModelConstants d} {P : LowSmoothnessTernaryConstants C} (k : ℕ) {η t : ℝ}
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ)
    (hvariance : η ^ 2 ≤ P.ρ) (T : BoundedEstimator C n)

include hη ht hfield hvariance in
theorem grid_lifted_observable_memLp :
    MemLp (gridLiftedObservable k P.a T.val) 2 (gridMixtureLaw d k n P.a P.v η t) := by
  let _ := grid_mixture_probability k n hη ht hfield hvariance
  apply MemLp.of_bound (gridLiftedObservable_measurable k P.a T.val).aestronglyMeasurable
    (effectiveVarianceUpper C)
  apply Filter.Eventually.of_forall
  intro z
  change |T.val.val (encodeDesignResponse P.a (z.1, z.2.2))| ≤ _
  rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property _).1)]
  exact (T.property _).2

def gridStateRisk {k : ℕ} (a v η t : ℝ) (T : Estimator d n)
    (ξ : TernaryVector (gridWindowCount d k)) (x : DesignSample d n) : ℝ :=
  ∑ y, finiteResponseLikelihood a
    (v - η ^ 2 * t) (gridSampleField d k n η x) ξ y *
      (T.val (encodeDesignResponse a (x, y)) - (v - η ^ 2 * t)) ^ 2

theorem grid_state_risk_integrable {k : ℕ} {η t : ℝ}
    (hη : 0 ≤ η) (ht : t ∈ Icc 0 1)
    (hfield : (2 ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (T : BoundedEstimator C n) (ξ : TernaryVector (gridWindowCount d k)) :
    Integrable (gridStateRisk P.a P.v η t T.val ξ)
      (Measure.pi (fun _ => cubeVolume d)) := by
  let _ := cubeVolume_isProbability d
  let V := P.v - η ^ 2 * t
  let B := (effectiveVarianceUpper C + |V|) ^ 2
  have hp x y  :=
    (grid_response_likelihood_pos k n hη ht hfield hvariance x ξ y).le
  have hb z : (T.val.val z - V) ^ 2 ≤ B := by
    have hab : |T.val.val z| ≤ effectiveVarianceUpper C := by
      rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property z).1)]
      exact (T.property z).2
    have he := (abs_sub (T.val.val z) V).trans (add_le_add hab (le_refl |V|))
    simpa using pow_le_pow_left₀ (abs_nonneg _) he 2
  have hm : Measurable (gridStateRisk P.a P.v η t T.val ξ) := by
    apply Finset.measurable_sum
    intro y _
    exact (finiteResponseLikelihood_measurable_comp _ _ _ measurable_const _
      (gridSampleField_coordinate_measurable d k n η) ξ y).mul
      (((T.val.property.comp (encodeDesignResponse_measurable P.a)).comp
        (measurable_id.prodMk measurable_const)).sub_const V |>.pow_const 2)
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun y _ => by bound))]
  calc
    _ ≤ _ :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hb _) (hp x y))
    _ = B := by
      rw [← Finset.sum_mul, finite_response_normalized _ _ _ _ _ _ P.a_pos.ne', one_mul]

theorem grid_mixture_risk_le_original_worstCase {k : ℕ} {η b t : ℝ}
    (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b)
    (hη : 0 ≤ η) (ht : t ∈ Icc 0 1)
    (hfield : (2 ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hscale : η = b / k ^ C.smoothness)
    (hholder : (2 ^ d + 68 * 2 ^ d * (d + 1)) * b ≤ C.holderBound)
    (T : BoundedEstimator C n) :
    (∫ z, (gridLiftedObservable k P.a T.val z - (P.v - η ^ 2 * t)) ^ 2
      ∂gridMixtureLaw d k n P.a P.v η t) ≤ (worstCaseRisk C T.val).toReal := by
  let _ := cubeVolume_isProbability d
  have hξ (ξ : TernaryVector (gridWindowCount d k)) :=
    grid_state_risk_integrable hη ht hfield hvariance T ξ
  unfold gridMixtureLaw
  rw [lowMixtureLaw_nonneg_integral_sum (V := (P.v - η ^ 2 * t))
    (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive ξ x hη ht hfield hvariance i y).le) ((gridLiftedObservable_measurable k P.a T.val).sub_const _ |>.pow_const 2)
    (fun _ => sq_nonneg _) hξ]
  calc
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ξ _
      apply mul_le_mul_of_nonneg_left
      · apply (ENNReal.ofReal_le_iff_le_toReal (boundedEstimator_worstCaseRisk_ne_top T)).mp
        exact gridPathParameter_finite_risk_le_worstCase ξ hk hs1 hb hη ht
          hfield hvariance hscale hholder T
      · exact Finset.prod_nonneg (fun j _ => activation_prior_nonnegative ht.1 ht.2 _)
    _ = _ := by rw [← Finset.sum_mul, activation_product_prior_normalized, one_mul]

def gridEncodedObservable (a : ℝ) (T : Estimator d n) :
    (DesignSample d n) → (TernaryVector n) → ℝ :=
  fun x y => T.val (encodeDesignResponse a (x, y))

theorem gridEncodedObservable_norm_le
    (a : ℝ) (T : BoundedEstimator C n) (x : DesignSample d n) :
    ‖gridEncodedObservable a T.val x‖ ≤ effectiveVarianceUpper C := by
  apply (pi_norm_le_iff_of_nonneg (C.varianceLower_pos.le.trans (effective_variance_interval_nondegenerate C).le)).mpr
  intro y
  change |T.val.val (encodeDesignResponse a (x, y))| ≤ _
  rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property _).1)]
  exact (T.property _).2

include hη ht hfield hvariance in
theorem grid_mixture_mean_eq :
    (∫ z, gridLiftedObservable k P.a T.val z ∂gridMixtureLaw d k n P.a P.v η t) =
      gridMixtureExpectation d k n P.a P.v η t (gridEncodedObservable P.a T.val) := by
  let _ := cubeVolume_isProbability d
  let _ := grid_mixture_probability k n hη ht hfield hvariance
  exact lowMixtureLaw_integral
    (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive ξ x hη ht hfield hvariance i y).le) ((grid_lifted_observable_memLp k hη ht hfield hvariance T).integrable (by norm_num))

include hη ht hfield hvariance in
theorem grid_mixture_score_observable_eq :
    (∫ z, gridLiftedObservable k P.a T.val z * gridMixtureScore d k n P.a P.v η t z
      ∂gridMixtureLaw d k n P.a P.v η t) =
      ∫ x, gridMixtureScoreObservable d k n P.a P.v η t (gridEncodedObservable P.a T.val) x
        ∂Measure.pi (fun _ => cubeVolume d) := by
  let _ := cubeVolume_isProbability d
  have hi := (grid_lifted_observable_memLp k hη ht hfield hvariance T).integrable_mul
    (grid_mixture_score_memLp k n hη ht hfield hvariance)
  simpa only [gridLiftedObservable, gridMixtureScore, gridMixtureLaw,
    gridMixtureScoreObservable, gridEncodedObservable, lowMixtureScore, Pi.mul_apply, mul_assoc,
    LowSmoothnessTernaryConstants.variancePath] using
    lowMixtureLaw_integral
      (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
      (fun x ξ i y => (grid_response_positive ξ x hη ht hfield hvariance i y).le) hi

end

variable {d n : ℕ} {C : ModelConstants d} {P : LowSmoothnessTernaryConstants C} {k : ℕ} {η b : ℝ}
    (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : ((2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)) * b ≤ C.holderBound)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) (hbudget : gridUniformScoreBudget P k n η ≤ 1)
include hb hbudget hfield hholder hk hmean hs1 hscale hvariance hη

/-- The complete actual-model score argument. All latent states obey the
original Hölder/moment class and all score and risk identities are derived. -/
theorem grid_prior_boundedEstimator_separation
    (T : BoundedEstimator C n) :
    η ^ 2 ≤ 3 * Real.sqrt ((worstCaseRisk C T.val).toReal) := by
  let r := Real.sqrt ((worstCaseRisk C T.val).toReal)
  let m := fun t => gridMixtureExpectation d k n P.a P.v η t (gridEncodedObservable P.a T.val)
  let m' := fun t => ∫ x,
    gridMixtureScoreObservable d k n P.a P.v η t (gridEncodedObservable P.a T.val) x
    ∂Measure.pi (fun _ => cubeVolume d)
  let sn := fun t => Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = (worstCaseRisk C T.val).toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hT := (by apply Measurable.of_eval; intro y; exact (T.val.property.comp (encodeDesignResponse_measurable P.a)).comp (measurable_id.prodMk measurable_const) : Measurable (gridEncodedObservable P.a ↑T))
  have hTB : ∀ᵐ x ∂Measure.pi (fun _ => cubeVolume d),
      ‖gridEncodedObservable P.a T.val x‖ ≤ effectiveVarianceUpper C :=
    Filter.Eventually.of_forall (gridEncodedObservable_norm_le P.a T)
  have hderiv t (ht : t ∈ Icc 0 1)  :=
    (grid_mixture_expectation_hasDerivAt k n
      hη ht hfield hvariance hT hTB).2
  have hderivI  :=
    grid_mixture_score_observable_intervalIntegrable k n
      hη hfield hvariance hT hTB
  have hscoreI  :=
    grid_sqrt_score_energy_intervalIntegrable hk hη hfield hvariance hmean
  have hris t (ht : t ∈ Icc 0 1) :
      (∫ z, (gridLiftedObservable k P.a T.val z - (P.v - η ^ 2 * t)) ^ 2
        ∂gridMixtureLaw d k n P.a P.v η t) ≤ r ^ 2 := by
    bound [grid_mixture_risk_le_original_worstCase hk hs1 hb hη ht hfield hvariance hscale hholder T]
  have hderivBound t (ht : t ∈ Icc 0 1) : |m' t| ≤ r * sn t := by
    let _ := grid_mixture_probability k n hη ht hfield hvariance
    have h := probability_score_bound
      (grid_lifted_observable_memLp k hη ht hfield hvariance T)
      (grid_mixture_score_memLp k n hη ht hfield hvariance) hr
      (grid_mixture_score_centered k n hη ht hfield hvariance) (hris t ht)
    rw [grid_mixture_score_observable_eq k hη ht hfield hvariance T,
      grid_mixture_score_energy k n hη ht hfield hvariance] at h
    exact h
  have hbias t (ht : t ∈ Icc 0 1) : |m t - (P.v - η ^ 2 * t)| ≤ r := by
    let _ := grid_mixture_probability k n hη ht hfield hvariance
    have h := probability_mean_error_le
      (grid_lifted_observable_memLp k hη ht hfield hvariance T) hr (hris t ht)
    rw [grid_mixture_mean_eq k hη ht hfield hvariance T] at h
    exact h
  have hsep := path_separation_le (by norm_num) hderiv hderivI hscoreI
    hderivBound (hbias 0 (by norm_num)) (hbias 1 (by norm_num))
  have hscoreBudget := by apply (grid_sqrt_score_energy_integral_le hk hη hfield hvariance hmean).trans; simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hbudget
  have he : |(P.v - η ^ 2 * 1) - (P.v - η ^ 2 * 0)| = η ^ 2 := by
    simp
  rw [he] at hsep
  exact hsep.trans (mul_le_mul_of_nonneg_right (by linarith) hr)

/-- Actual minimax RMS lower bound from the fully constructed grid prior. -/
theorem grid_prior_minimax_lower :
    ENNReal.ofReal (η ^ 2 / 3) ≤ minimaxRMS C n := by
  have hnonneg : 0 ≤ η ^ 2 / 3 := by positivity
  have hlower : ENNReal.ofReal (η ^ 2 / 3) ^ 2 ≤ minimaxRisk C n := by
    rw [minimaxRisk_eq_inf_bounded C n]
    apply le_iInf
    intro T
    rw [← ENNReal.ofReal_pow hnonneg 2]
    apply (ENNReal.ofReal_le_iff_le_toReal (boundedEstimator_worstCaseRisk_ne_top T)).mpr
    have hsep := grid_prior_boundedEstimator_separation hk hs1 hb hη
      hfield hvariance hscale hholder hmean hbudget T
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

end NearlyMinimax
