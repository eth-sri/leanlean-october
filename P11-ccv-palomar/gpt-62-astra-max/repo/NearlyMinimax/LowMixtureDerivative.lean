module

public import NearlyMinimax.LowSmoothness


@[expose] public section

/-! Differentiation of the actual finite latent experiment after integration
over a finite design measure. Uniform domination is proved from finite polynomial
formulas on a compact box; no bound on the score is assumed. -/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology BigOperators
namespace NearlyMinimax

abbrev FiniteExperimentData (m n : ℕ) :=
  ℝ × (((TernaryVector m) → Fin n → ℝ) × ((TernaryVector n) → ℝ))

section
variable {m n : ℕ} (a v η t : ℝ) (f : (TernaryVector m) → Fin n → ℝ) (T : (TernaryVector n) → ℝ)

def finiteExperimentRawDerivative : ℝ :=
  ∑ ξ, (activationProductPriorDerivative t ξ *
      (∑ y, finiteResponseLikelihood a (v - η ^ 2 * t) f ξ y * T y) +
    activationProductPrior t ξ *
      (∑ y, ((∑ i, finiteResponseVarianceTerm a (v - η ^ 2 * t) f ξ y i) *
        (-η ^ 2)) * T y))

theorem finite_experiment_raw_hasDerivAt :
    HasDerivAt (fun u => finiteExperimentExpectation a v η u f T)
      (finiteExperimentRawDerivative a v η t f T) t := by
  have hV : HasDerivAt (fun u => v - η ^ 2 * u) (-η ^ 2) t :=
    ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2))).congr_deriv (by ring)
  apply HasDerivAt.fun_sum
  intro ξ _
  apply (activation_product_prior_hasDerivAt t ξ).mul
  apply HasDerivAt.fun_sum
  intro y _
  exact ((finite_response_variance_hasDerivAt a (v - η ^ 2 * t) f ξ y).comp t hV).mul_const (T y)

end

@[fun_prop] theorem continuous_activationPriorMass (y : Fin 3) : Continuous (fun t => activationPriorMass t y) :=
  continuous_iff_continuousAt.mpr fun t => (activation_prior_hasDerivAt t y).continuousAt

section MeasurableExperiment
variable {α : Type*} [MeasurableSpace α] (m n : ℕ) (a : ℝ) {V : α → ℝ}
    (hV : Measurable V) (f : α → (TernaryVector m) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i))

include hf hV

variable (η : ℝ) (ξ : TernaryVector m) (y : TernaryVector n)

theorem finiteResponseLikelihood_measurable_comp :
    Measurable (fun x => finiteResponseLikelihood a (V x) (f x) ξ y) := by
  fun_prop [finiteResponseLikelihood]

theorem finiteExperimentScore_measurable_comp :
    Measurable (fun x => finiteExperimentScore a (V x) η (f x) ξ y) := by
  fun_prop [finiteExperimentScore, finiteExperimentScoreNumerator, latentDifference,
    finiteResponseLikelihood, finiteResponseVarianceTerm]

end MeasurableExperiment

section
variable (m n : ℕ) (a v η R : ℝ)

theorem finite_experiment_expectation_data_continuous :
    Continuous (fun z : FiniteExperimentData m n =>
      finiteExperimentExpectation a v η z.1 z.2.1 z.2.2) := by
  fun_prop [finiteExperimentExpectation, activationProductPrior, finiteResponseLikelihood]

theorem finite_experiment_raw_derivative_data_continuous :
    Continuous (fun z : FiniteExperimentData m n =>
      finiteExperimentRawDerivative a v η z.1 z.2.1 z.2.2) := by
  fun_prop [finiteExperimentRawDerivative, activationProductPriorDerivative, activationProductPrior,
    finiteResponseLikelihood, finiteResponseVarianceTerm]

/-- Both the expectation and its raw derivative are bounded on each finite
parameter box, including parameter values outside the probability interval. -/
theorem finite_experiment_uniform_box_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ t
      (f : (TernaryVector m) → Fin n → ℝ) T,
      |t| ≤ R → ‖f‖ ≤ R → ‖T‖ ≤ R →
      ‖finiteExperimentExpectation a v η t f T‖ ≤ B ∧
      ‖finiteExperimentRawDerivative a v η t f T‖ ≤ B := by
  have hG  := (finite_experiment_expectation_data_continuous m n a v η).prodMk
    (finite_experiment_raw_derivative_data_continuous m n a v η)
  obtain ⟨C, hC⟩ := (isCompact_closedBall 0 R).exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max 1 C, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  aesop

end

section Integrated
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

set_option maxHeartbeats 200000 in
/-- Bounded measurable fields and data observables can be differentiated after
integration over the actual design law. The domination needed for interchange
is derived from the finite polynomial formulas. -/
theorem finite_experiment_integrated_raw_hasDerivAt (m n : ℕ) (a v η t ρ M : ℝ)
    (f : α → (TernaryVector m) → Fin n → ℝ) (T : α → (TernaryVector n) → ℝ)
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ρ) (hTBound : ∀ᵐ x ∂μ, ‖T x‖ ≤ M) :
    Integrable (fun x => finiteExperimentRawDerivative a v η t (f x) (T x)) μ ∧
      HasDerivAt (fun u => ∫ x, finiteExperimentExpectation a v η u (f x) (T x) ∂μ)
        (∫ x, finiteExperimentRawDerivative a v η t (f x) (T x) ∂μ) t := by
  let R := max (|t| + 1) (max ρ M)
  obtain ⟨B, hB, hBox⟩ := finite_experiment_uniform_box_bound m n a v η R
  let F  := fun u x => finiteExperimentExpectation a v η u (f x) (T x)
  let D  := fun u x => finiteExperimentRawDerivative a v η u (f x) (T x)
  have hFData  :=
    (finite_experiment_expectation_data_continuous m n a v η).measurable
  have hDData  :=
    (finite_experiment_raw_derivative_data_continuous m n a v η).measurable
  have hFmeas u : Measurable (F u) := by
    fun_prop
  have hDmeas u : Measurable (D u) := by
    fun_prop
  have hFields : ∀ᵐ x ∂μ, ‖f x‖ ≤ R ∧ ‖T x‖ ≤ R := by
    filter_upwards [hfBound, hTBound] with x hfx hTx
    grind
  have hFint  := Integrable.of_bound (hFmeas t).aestronglyMeasurable B (by
    filter_upwards [hFields] with x hx
    grind)
  have hDom : ∀ᵐ x ∂μ, ∀ u ∈ ball t 1, ‖D u x‖ ≤ B := by
    filter_upwards [hFields] with x hx
    intro u hu
    have hut : ‖u - t‖ < 1 := by assumption
    have huR : |u| ≤ R := by
      have huNorm  := calc
        _ ≤ _ := norm_le_norm_sub_add u t
        _ ≤ _ := add_le_add hut.le le_rfl
        _ = |t| + 1 := by rw [Real.norm_eq_abs]; ring
      bound
    grind
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (ball_mem_nhds t (by norm_num))
    (Filter.Eventually.of_forall (fun u => (hFmeas u).aestronglyMeasurable)) hFint
    (hDmeas t).aestronglyMeasurable hDom (integrable_const B)
    (Filter.Eventually.of_forall (fun x u _ => finite_experiment_raw_hasDerivAt ..))

variable {m n : ℕ}

theorem finite_experiment_raw_derivative_eq_score {a v η t : ℝ}
    {f : (TernaryVector m) → Fin n → ℝ} (T : (TernaryVector n) → ℝ)
    (hpositive : ∀ ξ y, 0 < finiteResponseLikelihood a (v - η ^ 2 * t) f ξ y) :
    finiteExperimentRawDerivative a v η t f T =
      ∑ ξ, activationProductPrior t ξ * ∑ y,
        finiteResponseLikelihood a (v - η ^ 2 * t) f ξ y *
          T y * finiteExperimentScore a (v - η ^ 2 * t) η f ξ y :=
  (finite_experiment_raw_hasDerivAt a v η t f T).unique
    (finite_experiment_observable_score_hasDerivAt T hpositive)

/-- The integrated derivative is continuous, so its interval integrability
on a bounded parameter path is a consequence of the actual finite formulas. -/
theorem finite_experiment_integrated_raw_derivative_continuous (a v η : ℝ) {ρ M : ℝ}
    {f : α → (TernaryVector m) → Fin n → ℝ} {T : α → (TernaryVector n) → ℝ}
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ρ) (hTBound : ∀ᵐ x ∂μ, ‖T x‖ ≤ M) :
    Continuous (fun t => ∫ x, finiteExperimentRawDerivative a v η t (f x) (T x) ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let R := max (|t| + 1) (max ρ M)
  obtain ⟨B, hB, hBox⟩ := finite_experiment_uniform_box_bound m n a v η R
  let D  := fun u x => finiteExperimentRawDerivative a v η u (f x) (T x)
  have hDData  :=
    (finite_experiment_raw_derivative_data_continuous m n a v η).measurable
  have hDmeas u : Measurable (D u) := by
    fun_prop
  have hDom : ∀ᶠ u in 𝓝 t, ∀ᵐ x ∂μ, ‖D u x‖ ≤ B := by
    filter_upwards [ball_mem_nhds t (by norm_num : (0 : ℝ) < 1)] with u hu
    filter_upwards [hfBound, hTBound] with x hfx hTx
    have hut : ‖u - t‖ < 1 := by assumption
    have huR : |u| ≤ R := by
      have huNorm  := calc
        _ ≤ _ := norm_le_norm_sub_add u t
        _ ≤ _ := add_le_add hut.le le_rfl
        _ = |t| + 1 := by rw [Real.norm_eq_abs]; ring
      bound
    grind
  have hCont : ∀ᵐ x ∂μ, ContinuousAt (fun u => D u x) t := by
    apply Filter.Eventually.of_forall
    intro x
    have hDataCont : Continuous (fun u : ℝ => (u, (f x, T x))) :=
      continuous_id.prodMk continuous_const
    exact ((finite_experiment_raw_derivative_data_continuous m n a v η).comp hDataCont).continuousAt
  exact continuousAt_of_dominated
    (Filter.Eventually.of_forall (fun u => (hDmeas u).aestronglyMeasurable)) hDom (integrable_const B) hCont

/-- Exact score representation after integrating over the design. Likelihood
positivity is needed only at the differentiation point. -/
theorem finite_experiment_integrated_score_hasDerivAt {a v η t ρ M : ℝ}
    {f : α → (TernaryVector m) → Fin n → ℝ} {T : α → (TernaryVector n) → ℝ}
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ρ) (hTBound : ∀ᵐ x ∂μ, ‖T x‖ ≤ M)
    (hpositive : ∀ᵐ x ∂μ, ∀ ξ y,
      0 < finiteResponseLikelihood a (v - η ^ 2 * t) (f x) ξ y) :
    let S := fun x => ∑ ξ, activationProductPrior t ξ * ∑ y,
      finiteResponseLikelihood a (v - η ^ 2 * t) (f x) ξ y *
        T x y * finiteExperimentScore a (v - η ^ 2 * t) η (f x) ξ y
    Integrable S μ ∧ HasDerivAt
      (fun u => ∫ x, finiteExperimentExpectation a v η u (f x) (T x) ∂μ)
      (∫ x, S x ∂μ) t := by
  obtain ⟨hInt, hDeriv⟩ := finite_experiment_integrated_raw_hasDerivAt μ m n a v η t ρ M f T hf hT hfBound hTBound
  have he : (fun x => finiteExperimentRawDerivative a v η t (f x) (T x)) =ᵐ[μ]
      (fun x => ∑ ξ, activationProductPrior t ξ * ∑ y,
        finiteResponseLikelihood a (v - η ^ 2 * t) (f x) ξ y *
          T x y * finiteExperimentScore a (v - η ^ 2 * t) η (f x) ξ y) := by
    filter_upwards [hpositive] with x hx
    solve_by_elim [finite_experiment_raw_derivative_eq_score]
  exact ⟨hInt.congr he, (integral_congr_ae he) ▸ hDeriv⟩

end Integrated
end NearlyMinimax
