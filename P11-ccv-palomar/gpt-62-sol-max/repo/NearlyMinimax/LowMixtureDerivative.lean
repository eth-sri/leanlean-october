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
  ℝ × (((Fin m → Fin 3) → Fin n → ℝ) × ((Fin n → Fin 3) → ℝ))

def finiteExperimentRawDerivative (m n : ℕ) (a v η t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ) : ℝ :=
  ∑ ξ, activationProductPrior m t ξ * ∑ y,
    finiteExperimentScoreNumerator m n a (v - η ^ 2 * t) η f ξ y * T y

section
variable (m n : ℕ) (a v η t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ)

private theorem finite_marginal_likelihood_hasDerivAt (y : Fin n → Fin 3) :
    HasDerivAt (fun u => ∑ ξ, activationProductPrior m u ξ *
      finiteResponseLikelihood m n a (v - η ^ 2 * u) f ξ y)
      (∑ ξ, activationProductPrior m t ξ *
        finiteExperimentScoreNumerator m n a (v - η ^ 2 * t) η f ξ y) t := by
  let V := v - η ^ 2 * t
  have hV : HasDerivAt (fun u : ℝ => v - η ^ 2 * u) (-η ^ 2) t := ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2))).congr_deriv (by ring)
  have hF ξ := (finite_response_variance_hasDerivAt m n a V f ξ y).comp t hV
  have h := activation_expectation_hasDerivAt m t _ _ hF
  refine h.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [Finset.sum_add_distrib, activation_prior_derivative_replacement, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ξ _ => by
    simp only [finiteExperimentScoreNumerator]
    ring

theorem finite_experiment_raw_hasDerivAt (T : (Fin n → Fin 3) → ℝ) :
    HasDerivAt (fun u => finiteExperimentExpectation m n a v η u f T)
      (finiteExperimentRawDerivative m n a v η t f T) t := by
  convert HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n → Fin 3)))
    (fun y _ => (finite_marginal_likelihood_hasDerivAt m n a v η t f y).mul_const (T y)) using 1
  · funext u
    unfold finiteExperimentExpectation
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  · unfold finiteExperimentRawDerivative
    simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

end

section
variable {α : Type*} [MeasurableSpace α]
    (m n : ℕ)

theorem finiteResponseLikelihood_measurable_comp (a : ℝ) (V : α → ℝ) (hV : Measurable V)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i))
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) :
    Measurable (fun x => finiteResponseLikelihood m n a (V x) (f x) ξ y) := by
  fun_prop [finiteResponseLikelihood]

theorem finiteExperimentScore_measurable_comp (a η : ℝ) (V : α → ℝ) (hV : Measurable V)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i))
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) :
    Measurable (fun x => finiteExperimentScore m n a (V x) η (f x) ξ y) := by
  have hL := finiteResponseLikelihood_measurable_comp m n a V hV f hf
  have hU (i : Fin n) : Measurable (fun x =>
      finiteResponseVarianceTerm m n a (V x) (f x) ξ y i) := by
    fun_prop [finiteResponseVarianceTerm]
  have hD (j : Fin m) : Measurable (fun x => latentDifference m j
      (fun ξ' => finiteResponseLikelihood m n a (V x) (f x) ξ' y) ξ) := by
    fun_prop [latentDifference, finiteResponseLikelihood]
  exact ((Finset.measurable_sum _ (fun j _ => hD j)).sub
      ((Finset.measurable_sum _ (fun i _ => hU i)).const_mul (η ^ 2))).div (hL ξ y)

end

@[local fun_prop] theorem continuous_ternaryMass_comp {X : Type*} [TopologicalSpace X]
    {f V : X → ℝ} (hf : Continuous f) (hV : Continuous V) (a : ℝ) (y : Fin 3) :
    Continuous (fun x => ternaryMass a (f x) (V x) y) :=
  (ternaryMass_joint_continuous a y).comp (hf.prodMk hV)

@[local fun_prop] theorem activationPriorMass_continuous (y : Fin 3) :
    Continuous (fun t => activationPriorMass t y) := by
  fin_cases y <;> simp [activationPriorMass] <;> fun_prop

section
variable (m n : ℕ)

section
variable (a v η : ℝ)

theorem finite_experiment_expectation_data_continuous :
    Continuous (fun z : FiniteExperimentData m n =>
      finiteExperimentExpectation m n a v η z.1 z.2.1 z.2.2) := by
  unfold finiteExperimentExpectation activationProductPrior finiteResponseLikelihood
  fun_prop

theorem finite_experiment_raw_derivative_data_continuous :
    Continuous (fun z : FiniteExperimentData m n =>
      finiteExperimentRawDerivative m n a v η z.1 z.2.1 z.2.2) := by
  unfold finiteExperimentRawDerivative activationProductPrior finiteExperimentScoreNumerator
    latentDifference finiteResponseLikelihood finiteResponseVarianceTerm
  fun_prop

end

/-- Both the expectation and its raw derivative are bounded on each finite
parameter box, including parameter values outside the probability interval. -/
theorem finite_experiment_uniform_box_bound (a v η R : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (t : ℝ)
      (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ),
      |t| ≤ R → ‖f‖ ≤ R → ‖T‖ ≤ R →
      ‖finiteExperimentExpectation m n a v η t f T‖ ≤ B ∧
      ‖finiteExperimentRawDerivative m n a v η t f T‖ ≤ B := by
  have hG := (finite_experiment_expectation_data_continuous m n a v η).prodMk
    (finite_experiment_raw_derivative_data_continuous m n a v η)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : FiniteExperimentData m n) R).exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max 1 C, (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _), ?_⟩
  intro t f T ht hf hT
  have hz : (t, (f, T)) ∈ closedBall (0 : FiniteExperimentData m n) R := by
    rw [mem_closedBall, dist_zero_right]
    exact norm_prod_le_iff.mpr ⟨by assumption,
      norm_prod_le_iff.mpr ⟨hf, hT⟩⟩
  exact norm_prod_le_iff.mp ((hC _ hz).trans (le_max_right _ _))

end

section Integrated
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

attribute [local irreducible] finiteExperimentExpectation finiteExperimentRawDerivative in
/-- Bounded measurable fields and data observables can be differentiated after
integration over the actual design law. The domination needed for interchange
is derived from the finite polynomial formulas. -/
private theorem finite_experiment_integrated_raw_hasDerivAt (m n : ℕ) (a v η t ρ M : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (T : α → (Fin n → Fin 3) → ℝ)
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ρ) (hTBound : ∀ᵐ x ∂μ, ‖T x‖ ≤ M) :
    HasDerivAt (fun u => ∫ x, finiteExperimentExpectation m n a v η u (f x) (T x) ∂μ)
      (∫ x, finiteExperimentRawDerivative m n a v η t (f x) (T x) ∂μ) t := by
  let R := max (|t| + 1) (max ρ M)
  obtain ⟨B, hB, hBox⟩ := finite_experiment_uniform_box_bound m n a v η R
  let F := fun u x => finiteExperimentExpectation m n a v η u (f x) (T x)
  let D := fun u x => finiteExperimentRawDerivative m n a v η u (f x) (T x)
  have hm (u : ℝ) : Measurable (fun x => (u, (f x, T x))) := measurable_const.prodMk (hf.prodMk hT)
  have hF (u : ℝ) : AEStronglyMeasurable (F u) μ :=
    ((finite_experiment_expectation_data_continuous m n a v η).measurable.comp (hm u)).aestronglyMeasurable
  have hD (u : ℝ) : AEStronglyMeasurable (D u) μ :=
    ((finite_experiment_raw_derivative_data_continuous m n a v η).measurable.comp (hm u)).aestronglyMeasurable
  have hab : ball t 1 ∈ 𝓝 t := ball_mem_nhds t (by norm_num)
  have hb : ∀ᵐ x ∂μ, ∀ u ∈ ball t 1, ‖F u x‖ ≤ B ∧ ‖D u x‖ ≤ B := by
    filter_upwards [hfBound, hTBound] with x hfx hTx
    intro u hu
    have hut : ‖u - t‖ < 1 := hu
    have huR : |u| ≤ R := (norm_le_norm_sub_add u t).trans (by
      rw [Real.norm_eq_abs t]
      exact (by linarith : ‖u - t‖ + |t| ≤ |t| + 1).trans (le_max_left _ _))
    exact hBox u (f x) (T x) huR
      (hfx.trans ((le_max_left ρ M).trans (le_max_right _ _)))
      (hTx.trans ((le_max_right ρ M).trans (le_max_right _ _)))
  have hi := Integrable.of_bound (hF t) B (hb.mono fun _ hx => (hx t (mem_of_mem_nhds hab)).1)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := F) (F' := D)
    hab (.of_forall hF) hi (hD t) (hb.mono fun x hx u hu => (hx u hu).2) (integrable_const B)
    (.of_forall fun x u _ => finite_experiment_raw_hasDerivAt m n a v η u (f x) (T x))).2

section
variable (m n : ℕ)

theorem finite_experiment_raw_derivative_eq_score (a v η t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ)
    (hpositive : ∀ ξ y, 0 < finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y) :
    finiteExperimentRawDerivative m n a v η t f T =
      ∑ ξ, activationProductPrior m t ξ * ∑ y,
        finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y *
          T y * finiteExperimentScore m n a (v - η ^ 2 * t) η f ξ y := by
  grind [finiteExperimentScore, activationProductPrior, finiteResponseLikelihood, finiteExperimentRawDerivative]

/-- Exact score representation after integrating over the design. Likelihood
positivity is needed only at the differentiation point. -/
theorem finite_experiment_integrated_score_hasDerivAt (a v η t ρ M : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (T : α → (Fin n → Fin 3) → ℝ)
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ρ) (hTBound : ∀ᵐ x ∂μ, ‖T x‖ ≤ M)
    (hpositive : ∀ᵐ x ∂μ, ∀ ξ y,
      0 < finiteResponseLikelihood m n a (v - η ^ 2 * t) (f x) ξ y) :
    let S := fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
      finiteResponseLikelihood m n a (v - η ^ 2 * t) (f x) ξ y *
        T x y * finiteExperimentScore m n a (v - η ^ 2 * t) η (f x) ξ y
    HasDerivAt
      (fun u => ∫ x, finiteExperimentExpectation m n a v η u (f x) (T x) ∂μ)
      (∫ x, S x ∂μ) t := by
  dsimp only
  have hDeriv := finite_experiment_integrated_raw_hasDerivAt μ m n a v η t ρ M f T hf hT hfBound hTBound
  have he : (fun x => finiteExperimentRawDerivative m n a v η t (f x) (T x)) =ᵐ[μ]
      (fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
        finiteResponseLikelihood m n a (v - η ^ 2 * t) (f x) ξ y *
          T x y * finiteExperimentScore m n a (v - η ^ 2 * t) η (f x) ξ y) := by
    filter_upwards [hpositive] with x hx
    apply finite_experiment_raw_derivative_eq_score <;> assumption
  exact (integral_congr_ae he) ▸ hDeriv

end

end Integrated
end NearlyMinimax
