module
public import NearlyMinimax.LowMixtureLaw
public import NearlyMinimax.PairWindowModel
public import NearlyMinimax.StabilizedRatioRisk
public import NearlyMinimax.PaperGoals
@[expose] public section
noncomputable section
open MeasureTheory Set Filter Metric ProbabilityTheory
open scoped Topology BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
section
variable {d : ℕ}
abbrev FiniteExperimentData (m n : ℕ) :=
  ℝ × (((Fin m → Fin 3) → Fin n → ℝ) × ((Fin n → Fin 3) → ℝ))
def finiteExperimentRawDerivative (m n ) (a v η t : ℝ)
    (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ) : ℝ :=
  ∑ ξ, (activationProductPriorDerivative m t ξ *
      (∑ y, finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y * T y) +
    activationProductPrior m t ξ *
      (∑ y, ((∑ i, finiteResponseVarianceTerm m n a (v - η ^ 2 * t) f ξ y i) *
        (-η ^ 2)) * T y))
theorem finite_experiment_raw_hasDerivAt (m n a v η t f T) :
    HasDerivAt (fun u => finiteExperimentExpectation m n a v η u f T)
      (finiteExperimentRawDerivative m n a v η t f T) t := by
  have hV : HasDerivAt (fun u => v - η ^ 2 * u) (-η ^ 2) t :=
    ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2))).congr_deriv (by ring)
  unfold finiteExperimentExpectation finiteExperimentRawDerivative
  apply HasDerivAt.fun_sum
  intro ξ _
  apply (activation_product_prior_hasDerivAt m t ξ).mul
  apply HasDerivAt.fun_sum
  intro y _
  exact ((finite_response_variance_hasDerivAt m n a (v - η ^ 2 * t) f ξ y).comp t hV).mul_const (T y)
theorem ternaryMass_joint_continuous (a : ℝ) (y : Fin 3) :
    Continuous (fun z : ℝ × ℝ => ternaryMass a z.1 z.2 y) := by
  fin_cases y <;> simp [ternaryMass] <;> fun_prop
theorem finite_response_data_continuous (m n a v η ξ y) :
    Continuous (fun z : FiniteExperimentData m n =>
      finiteResponseLikelihood m n a (v - η ^ 2 * z.1) z.2.1 ξ y) := by
  apply continuous_finset_prod
  intro i _
  exact (ternaryMass_joint_continuous a (y i)).comp
    ((show Continuous (fun z : FiniteExperimentData m n => z.2.1 ξ i) from by fun_prop).prodMk
      (show Continuous (fun z : FiniteExperimentData m n => v - η ^ 2 * z.1) from by fun_prop))
theorem finite_experiment_expectation_data_continuous (m n a v η) :
    Continuous (fun z : FiniteExperimentData m n =>
      finiteExperimentExpectation m n a v η z.1 z.2.1 z.2.2) := by
  apply continuous_finset_sum
  intro ξ _
  apply Continuous.mul
  · exact (continuous_iff_continuousAt.mpr (fun t =>
      (activation_product_prior_hasDerivAt m t ξ).continuousAt)).comp continuous_fst
  · apply continuous_finset_sum
    intro y _
    exact (finite_response_data_continuous m n a v η ξ y).mul
      ((continuous_apply y).comp (continuous_snd.comp continuous_snd))
theorem finite_experiment_raw_derivative_data_continuous (m n a v η) :
    Continuous (fun z : FiniteExperimentData m n =>
      finiteExperimentRawDerivative m n a v η z.1 z.2.1 z.2.2) := by
  apply continuous_finset_sum
  intro ξ _
  apply Continuous.add
  · apply Continuous.mul
    · unfold activationProductPriorDerivative
      apply continuous_finset_sum
      intro j _
      apply Continuous.const_mul
      apply continuous_finset_prod
      intro k _
      exact (continuous_iff_continuousAt.mpr (fun t =>
        (activation_prior_hasDerivAt t (ξ k)).continuousAt)).comp continuous_fst
    · apply continuous_finset_sum
      intro y _
      exact (finite_response_data_continuous m n a v η ξ y).mul
        ((continuous_apply y).comp (continuous_snd.comp continuous_snd))
  · apply Continuous.mul
    · exact (continuous_iff_continuousAt.mpr (fun t =>
        (activation_product_prior_hasDerivAt m t ξ).continuousAt)).comp continuous_fst
    · apply continuous_finset_sum
      intro y _
      apply Continuous.mul
      · apply Continuous.mul_const
        apply continuous_finset_sum
        intro i _
        have h_finite_variance_data_continuous : Continuous (fun z : FiniteExperimentData m n =>
            finiteResponseVarianceTerm m n a (v - η ^ 2 * z.1) z.2.1 ξ y i) := by
          apply Continuous.const_mul
          apply continuous_finset_prod
          intro k _
          exact (ternaryMass_joint_continuous a (y k)).comp
            ((show Continuous (fun z : FiniteExperimentData m n => z.2.1 ξ k) from by fun_prop).prodMk
              (show Continuous (fun z : FiniteExperimentData m n => v - η ^ 2 * z.1) from by fun_prop))
        exact h_finite_variance_data_continuous
      · exact (continuous_apply y).comp (continuous_snd.comp continuous_snd)
theorem finite_experiment_uniform_box_bound (m n a v η R) :
    ∃ B : ℝ, 0 < B ∧ ∀ (t : ℝ)
      (f : (Fin m → Fin 3) → Fin n → ℝ) (T : (Fin n → Fin 3) → ℝ),
      |t| ≤ R → ‖f‖ ≤ R → ‖T‖ ≤ R →
      ‖finiteExperimentExpectation m n a v η t f T‖ ≤ B ∧
      ‖finiteExperimentRawDerivative m n a v η t f T‖ ≤ B := by
  have hG  := (finite_experiment_expectation_data_continuous m n a v η).prodMk
    (finite_experiment_raw_derivative_data_continuous m n a v η)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : FiniteExperimentData m n) R).exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max 1 C, (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _), ?_⟩
  intro t f T ht hf hT
  have hz : (t, (f, T)) ∈ closedBall (0 : FiniteExperimentData m n) R := by
    rw [mem_closedBall, dist_zero_right]
    exact norm_prod_le_iff.mpr ⟨by simpa only [Real.norm_eq_abs] using ht,
      norm_prod_le_iff.mpr ⟨hf, hT⟩⟩
  exact norm_prod_le_iff.mp ((hC _ hz).trans (le_max_right _ _))
section Integrated
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
set_option maxHeartbeats 200000 in
theorem finite_experiment_raw_derivative_eq_score (m n a v η t f T)
    (hpositive : ∀ ξ y, 0 < finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y) :
    finiteExperimentRawDerivative m n a v η t f T =
      ∑ ξ, activationProductPrior m t ξ * ∑ y,
        finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y *
          T y * finiteExperimentScore m n a (v - η ^ 2 * t) η f ξ y :=
  have h_finite_experiment_observable_score_hasDerivAt : HasDerivAt (fun u => finiteExperimentExpectation m n a v η u f T)
      (∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
        ∑ y : Fin n → Fin 3, finiteResponseLikelihood m n a (v - η ^ 2 * t) f ξ y *
          T y * finiteExperimentScore m n a (v - η ^ 2 * t) η f ξ y) t := by
    have h_activation_coordinate_sum (j) (r : Fin 3 → ℝ) (F : (Fin m → Fin 3) → ℝ) : (∑ ξ : Fin m → Fin 3, r (ξ j) *
        (∏ k ∈ (Finset.univ : Finset (Fin m)).erase j, activationPriorMass t (ξ k)) * F ξ) =
        ∑ u : ({k : Fin m // k ≠ j} → Fin 3),
          (∏ k : {k : Fin m // k ≠ j}, activationPriorMass t (u k)) *
            ∑ z : Fin 3, r z * F ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) := by
      have hrest (z : Fin 3) (u : {k : Fin m // k ≠ j} → Fin 3) :
          (∏ k ∈ (Finset.univ : Finset (Fin m)).erase j,
            activationPriorMass t ((Equiv.funSplitAt j (Fin 3)).symm (z, u) k)) =
            ∏ k : {k : Fin m // k ≠ j}, activationPriorMass t (u k) := by
        rw [Finset.prod_subtype (p := fun k => k ≠ j) _ (by simp [eq_comm])]
        apply Finset.prod_congr rfl
        intro k _
        simp [Equiv.funSplitAt_symm_apply, k.property]
      rw [← (Equiv.funSplitAt j (Fin 3)).symm.sum_comp, Fintype.sum_prod_type]
      simp_rw [hrest]
      simp only [Equiv.funSplitAt_symm_apply, dite_true]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    let V := v - η ^ 2 * t
    let L : (Fin m → Fin 3) → (Fin n → Fin 3) → ℝ :=
      finiteResponseLikelihood m n a V f
    let U : (Fin m → Fin 3) → (Fin n → Fin 3) → ℝ :=
      fun ξ y => ∑ i, finiteResponseVarianceTerm m n a V f ξ y i
    have hV : HasDerivAt (fun u : ℝ => v - η ^ 2 * u) (-η ^ 2) t :=
      ((hasDerivAt_const t v).sub ((hasDerivAt_id t).const_mul (η ^ 2))).congr_deriv (by ring)
    have hF : ∀ ξ : Fin m → Fin 3,
        HasDerivAt (fun u => ∑ y : Fin n → Fin 3,
          finiteResponseLikelihood m n a (v - η ^ 2 * u) f ξ y * T y)
          (-η ^ 2 * ∑ y : Fin n → Fin 3, U ξ y * T y) t := by
      intro ξ
      have hy : ∀ y : Fin n → Fin 3,
          HasDerivAt (fun u => finiteResponseLikelihood m n a (v - η ^ 2 * u) f ξ y * T y)
            ((-η ^ 2 * U ξ y) * T y) t := by
        intro y
        have hcomp : HasDerivAt
            (fun u => finiteResponseLikelihood m n a (v - η ^ 2 * u) f ξ y)
            (-η ^ 2 * U ξ y) t :=
          (by
            have hcomp0 := (finite_response_variance_hasDerivAt m n a
              (v - η ^ 2 * t) f ξ y).comp t hV
            exact hcomp0.congr_deriv (by dsimp [U, V]; ring))
        exact hcomp.mul_const (T y)
      convert HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n → Fin 3)))
        (fun y _ => hy y) using 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    have h_activation_expectation_hasDerivAt := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin m → Fin 3)))
        (fun ξ _ =>
        (activation_product_prior_hasDerivAt m t ξ).mul (hF ξ))
    have h := h_activation_expectation_hasDerivAt
    change HasDerivAt _ _ t at h
    apply h.congr_deriv
    have h_activation_prior_derivative_replacement (F : (Fin m → Fin 3) → ℝ) : (∑ ξ : Fin m → Fin 3, activationProductPriorDerivative m t ξ * F ξ) =
        ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ * ∑ j, latentDifference m j F ξ := by
      unfold activationProductPriorDerivative
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      conv_lhs => rw [Finset.sum_comm]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      have hupdate (z z' : Fin 3) (u : {k : Fin m // k ≠ j} → Fin 3) :
          Function.update ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) j z' =
            (Equiv.funSplitAt j (Fin 3)).symm (z', u) := by
        funext k
        by_cases h : k = j
        · subst k
          simp [Equiv.funSplitAt_symm_apply]
        · simp [Equiv.funSplitAt_symm_apply, h]
      have hD (z : Fin 3) (u : {k : Fin m // k ≠ j} → Fin 3) :
          latentDifference m j F ((Equiv.funSplitAt j (Fin 3)).symm (z, u)) =
            ∑ z' : Fin 3, activationPriorDerivative z' *
              F ((Equiv.funSplitAt j (Fin 3)).symm (z', u)) := by
        have h_latent_difference_eq_signed_sum (ξ : Fin m → Fin 3) : latentDifference m j F ξ =
          ∑ z : Fin 3, activationPriorDerivative z * F (Function.update ξ j z) := by
          simp [latentDifference, Fin.sum_univ_succ, activationPriorDerivative]
          ring
        rw [h_latent_difference_eq_signed_sum]
        simp_rw [hupdate]
      simp_rw [activation_prior_factor m t _ j]
      rw [h_activation_coordinate_sum j activationPriorDerivative F,
        h_activation_coordinate_sum j (activationPriorMass t) (latentDifference m j F)]
      apply Finset.sum_congr rfl
      intro u _
      simp_rw [hD]
      rw [← Finset.sum_mul, activation_prior_normalized]
      simp
    have hprior := h_activation_prior_derivative_replacement (fun ξ => ∑ y : Fin n → Fin 3, L ξ y * T y)
    have hscore : ∀ ξ y,
        L ξ y * T y * finiteExperimentScore m n a V η f ξ y =
          ((∑ j, latentDifference m j (fun ξ' => L ξ' y) ξ) - η ^ 2 * U ξ y) * T y := by
      intro ξ y
      dsimp [L, U, finiteExperimentScore, finiteExperimentScoreNumerator]
      have hL : finiteResponseLikelihood m n a V f ξ y ≠ 0 := ne_of_gt (hpositive ξ y)
      field_simp [hL]
    change (∑ ξ : Fin m → Fin 3,
        (activationProductPriorDerivative m t ξ * (∑ y, L ξ y * T y) +
          activationProductPrior m t ξ * (-η ^ 2 * ∑ y, U ξ y * T y))) =
        ∑ ξ : Fin m → Fin 3, activationProductPrior m t ξ *
          ∑ y : Fin n → Fin 3, L ξ y * T y * finiteExperimentScore m n a V η f ξ y
    rw [Finset.sum_add_distrib, hprior]
    have hDsum (ξ : Fin m → Fin 3) :
        (∑ j, latentDifference m j (fun ξ' => ∑ y, L ξ' y * T y) ξ) =
          ∑ y, (∑ j, latentDifference m j (fun ξ' => L ξ' y) ξ) * T y := by
      simp_rw [latent_difference_response_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_mul]
    simp_rw [hDsum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ξ _
    simp_rw [hscore]
    rw [← mul_add]
    congr 1
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y _
    ring
  (finite_experiment_raw_hasDerivAt m n a v η t f T).unique
    h_finite_experiment_observable_score_hasDerivAt
theorem finite_experiment_integrated_raw_derivative_continuous (m n a v η ρ M f T)
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ρ) (hTBound : ∀ᵐ x ∂μ, ‖T x‖ ≤ M) :
    Continuous (fun t => ∫ x, finiteExperimentRawDerivative m n a v η t (f x) (T x) ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let R := max (|t| + 1) (max ρ M)
  obtain ⟨B, hB, hBox⟩ := finite_experiment_uniform_box_bound m n a v η R
  let D : ℝ → α → ℝ := fun u x => finiteExperimentRawDerivative m n a v η u (f x) (T x)
  have hData (u : ℝ) : Measurable (fun x : α => (u, (f x, T x))) :=
    measurable_const.prodMk (hf.prodMk hT)
  have hDData  :=
    (finite_experiment_raw_derivative_data_continuous m n a v η).measurable
  have hDmeas u : Measurable (D u) := by
    have hComp := hDData.comp (hData u)
    exact hComp
  have hDom : ∀ᶠ u in 𝓝 t, ∀ᵐ x ∂μ, ‖D u x‖ ≤ B := by
    filter_upwards [ball_mem_nhds t (by norm_num : (0 : ℝ) < 1)] with u hu
    filter_upwards [hfBound, hTBound] with x hfx hTx
    have hut : ‖u - t‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hu
    have huR : |u| ≤ R := by
      have huNorm  := calc
        ‖u‖ ≤ ‖u - t‖ + ‖t‖ := norm_le_norm_sub_add u t
        _ ≤ 1 + ‖t‖ := add_le_add hut.le le_rfl
        _ = |t| + 1 := by rw [Real.norm_eq_abs]; ring
      have huAbs : |u| ≤ |t| + 1 := by simpa only [Real.norm_eq_abs] using huNorm
      exact huAbs.trans (le_max_left _ _)
    exact (hBox u (f x) (T x) huR
      (hfx.trans ((le_max_left ρ M).trans (le_max_right _ _)))
      (hTx.trans ((le_max_right ρ M).trans (le_max_right _ _)))).2
  have hCont : ∀ᵐ x ∂μ, ContinuousAt (fun u => D u x) t := by
    apply Filter.Eventually.of_forall
    intro x
    have hDataCont : Continuous (fun u : ℝ => (u, (f x, T x))) :=
      continuous_id.prodMk continuous_const
    have hComp := (finite_experiment_raw_derivative_data_continuous m n a v η).comp hDataCont
    exact hComp.continuousAt
  exact continuousAt_of_dominated (F := D) (bound := fun _ => B)
    (Filter.Eventually.of_forall (fun u => (hDmeas u).aestronglyMeasurable)) hDom (integrable_const B) hCont
theorem finite_experiment_integrated_score_hasDerivAt (m n a v η t ρ M f) (T : α → (Fin n → Fin 3) → ℝ)
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : ∀ᵐ x ∂μ, ‖f x‖ ≤ ρ) (hTBound : ∀ᵐ x ∂μ, ‖T x‖ ≤ M)
    (hpositive : ∀ᵐ x ∂μ, ∀ ξ y,
      0 < finiteResponseLikelihood m n a (v - η ^ 2 * t) (f x) ξ y) :
    let S := fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
      finiteResponseLikelihood m n a (v - η ^ 2 * t) (f x) ξ y *
        T x y * finiteExperimentScore m n a (v - η ^ 2 * t) η (f x) ξ y
    Integrable S μ ∧ HasDerivAt
      (fun u => ∫ x, finiteExperimentExpectation m n a v η u (f x) (T x) ∂μ)
      (∫ x, S x ∂μ) t := by
  let R := max (|t| + 1) (max ρ M)
  obtain ⟨B, hB, hBox⟩ := finite_experiment_uniform_box_bound m n a v η R
  let F : ℝ → α → ℝ := fun u x => finiteExperimentExpectation m n a v η u (f x) (T x)
  let D : ℝ → α → ℝ := fun u x => finiteExperimentRawDerivative m n a v η u (f x) (T x)
  have hData (u : ℝ) : Measurable (fun x : α => (u, (f x, T x))) :=
    measurable_const.prodMk (hf.prodMk hT)
  have hFmeas u : Measurable (F u) := by
    have hComp := ((finite_experiment_expectation_data_continuous m n a v η).measurable).comp (hData u)
    exact hComp
  have hDmeas u : Measurable (D u) := by
    have hComp := ((finite_experiment_raw_derivative_data_continuous m n a v η).measurable).comp (hData u)
    exact hComp
  have hFields : ∀ᵐ x ∂μ, ‖f x‖ ≤ R ∧ ‖T x‖ ≤ R := by
    filter_upwards [hfBound, hTBound] with x hfx hTx
    exact ⟨hfx.trans ((le_max_left ρ M).trans (le_max_right _ _)),
      hTx.trans ((le_max_right ρ M).trans (le_max_right _ _))⟩
  have hFint  := Integrable.of_bound (hFmeas t).aestronglyMeasurable B (by
    filter_upwards [hFields] with x hx
    exact (hBox t (f x) (T x) ((le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (le_max_left _ _)) hx.1 hx.2).1)
  have hDom : ∀ᵐ x ∂μ, ∀ u ∈ ball t 1, ‖D u x‖ ≤ B := by
    filter_upwards [hFields] with x hx
    intro u hu
    have hut : ‖u - t‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hu
    have huR : |u| ≤ R := by
      have huNorm  := calc
        ‖u‖ ≤ ‖u - t‖ + ‖t‖ := norm_le_norm_sub_add u t
        _ ≤ 1 + ‖t‖ := add_le_add hut.le le_rfl
        _ = |t| + 1 := by rw [Real.norm_eq_abs]; ring
      have huAbs : |u| ≤ |t| + 1 := by simpa only [Real.norm_eq_abs] using huNorm
      exact huAbs.trans (le_max_left _ _)
    exact (hBox u (f x) (T x) huR hx.1 hx.2).2
  have h_finite_experiment_integrated_raw_hasDerivAt := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (F := F) (F' := D) (bound := fun _ => B) (s := ball t 1)
      (ball_mem_nhds t (by norm_num))
      (Filter.Eventually.of_forall (fun u => (hFmeas u).aestronglyMeasurable)) hFint
      (hDmeas t).aestronglyMeasurable hDom (integrable_const B)
      (Filter.Eventually.of_forall (fun x u _ => finite_experiment_raw_hasDerivAt m n a v η u (f x) (T x)))
  obtain ⟨hInt, hDeriv⟩ := h_finite_experiment_integrated_raw_hasDerivAt
  have he : (fun x => finiteExperimentRawDerivative m n a v η t (f x) (T x)) =ᵐ[μ]
      (fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
        finiteResponseLikelihood m n a (v - η ^ 2 * t) (f x) ξ y *
          T x y * finiteExperimentScore m n a (v - η ^ 2 * t) η (f x) ξ y) := by
    filter_upwards [hpositive] with x hx
    exact finite_experiment_raw_derivative_eq_score m n a v η t (f x) (T x) hx
  exact ⟨hInt.congr he, (integral_congr_ae he) ▸ hDeriv⟩
end Integrated
def gridSampleField (d k n ) (η : ℝ) (x : Fin n → Covariate d) :
    (Fin (gridWindowCount d k) → Fin 3) → Fin n → ℝ :=
  fun ξ i => indexedGridField d k η ξ (x i)
theorem gridSampleField_measurable (d k n η) :
    Measurable (gridSampleField d k n η) := by
  apply measurable_pi_lambda
  intro ξ
  apply measurable_pi_lambda
  intro i
  have h := (indexedGridField_continuous d k η ξ).measurable.comp
    (show Measurable (fun x : Fin n → Covariate d => x i) from measurable_pi_apply i)
  exact h
theorem gridSampleField_norm_le (d k n η) (hη : 0 ≤ η)
    (x ) : ‖gridSampleField d k n η x‖ ≤ 2 ^ d * η := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro ξ
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  simpa only [gridSampleField, Real.norm_eq_abs] using indexedGridField_abs_bound d k η hη ξ (x i)
def gridMixtureExpectation (d k n : ℕ) (a v η t : ℝ)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ) : ℝ :=
  ∫ x, finiteExperimentExpectation (gridWindowCount d k) n a v η t
    (gridSampleField d k n η x) (T x) ∂Measure.pi (fun _ => cubeVolume d)
def gridMixtureScoreObservable (d k n : ℕ) (a v η t : ℝ)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ)
    (x : Fin n → Covariate d) : ℝ :=
  ∑ ξ, activationProductPrior (gridWindowCount d k) t ξ * ∑ y,
    finiteResponseLikelihood (gridWindowCount d k) n a (v - η ^ 2 * t)
      (gridSampleField d k n η x) ξ y * T x y *
    finiteExperimentScore (gridWindowCount d k) n a (v - η ^ 2 * t) η
      (gridSampleField d k n η x) ξ y
theorem grid_response_likelihood_pos  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (x : Fin n → Covariate d) (ξ : Fin (gridWindowCount d k) → Fin 3) (y : Fin n → Fin 3) :
    0 < finiteResponseLikelihood (gridWindowCount d k) n P.a (P.v - η ^ 2 * t)
      (gridSampleField d k n η x) ξ y := by
  apply Finset.prod_pos
  intro i _
  exact P.c_pos.trans_le ((P.path_legality η t _ ht hvariance ((indexedGridField_abs_bound d k η hη ξ (x i)).trans (by nlinarith))).2.2.1 (y i))
theorem grid_mixture_expectation_hasDerivAt  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t M : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ) (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => cubeVolume d), ‖T x‖ ≤ M) :
    Integrable (gridMixtureScoreObservable d k n P.a P.v η t T)
        (Measure.pi (fun _ : Fin n => cubeVolume d)) ∧
      HasDerivAt (fun u => gridMixtureExpectation d k n P.a P.v η u T)
        (∫ x, gridMixtureScoreObservable d k n P.a P.v η t T x
          ∂Measure.pi (fun _ : Fin n => cubeVolume d)) t := by
  let _ := cubeVolume_isProbability d
  exact finite_experiment_integrated_score_hasDerivAt
    (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n P.a P.v η t
    (↑2 ^ d * η) M (gridSampleField d k n η) T
    (gridSampleField_measurable d k n η) hT
    (Filter.Eventually.of_forall (gridSampleField_norm_le d k n η hη)) hTBound
    (Filter.Eventually.of_forall (grid_response_likelihood_pos C P k n η t hη ht hfield hvariance))
theorem grid_mixture_score_observable_intervalIntegrable  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η M : ℝ)
    (hη : 0 ≤ η) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (T : (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ) (hT : Measurable T)
    (hTBound : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => cubeVolume d), ‖T x‖ ≤ M) :
    IntervalIntegrable (fun t => ∫ x, gridMixtureScoreObservable d k n P.a P.v η t T x
      ∂Measure.pi (fun _ : Fin n => cubeVolume d)) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num : (0 : ℝ) ≤ 1)
  let _ := cubeVolume_isProbability d
  have h_grid_mixture_raw_derivative_continuous := finite_experiment_integrated_raw_derivative_continuous
      (Measure.pi (fun _ => cubeVolume d)) (gridWindowCount d k) n P.a P.v η (2 ^ d * η) M
      (gridSampleField d k n η) T (gridSampleField_measurable d k n η) hT
      (Filter.Eventually.of_forall (gridSampleField_norm_le d k n η hη)) hTBound
  apply h_grid_mixture_raw_derivative_continuous.continuousOn.congr
  intro t ht
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  exact (finite_experiment_raw_derivative_eq_score (gridWindowCount d k) n P.a P.v η t
    (gridSampleField d k n η x) (T x)
    (grid_response_likelihood_pos C P k n η t hη ht hfield hvariance x)).symm
def gridUniformScoreBudget  {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η : ℝ) : ℝ :=
  ↑40 ^ d * ternaryScoreExponentialConstant P.a P.ρ P.c ^ 2 *
    Real.exp (ternaryScoreExponentialConstant P.a P.ρ P.c) * n ^ 2 * η ^ 4 / ↑k ^ d
theorem grid_sqrt_score_energy_intervalIntegrable  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η : ℝ) (hk : 1 ≤ k)
    (hη : 0 ≤ η) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) :
    IntervalIntegrable (fun t => Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) volume 0 1 := by
  have h_grid_prior_score_energy_path_measurable : Measurable (gridPriorScoreEnergy d k n P.a P.v η) := by
    let _ := cubeVolume_isProbability d
    apply Finset.measurable_sum
    intro ξ _
    have hPrior  :=
      (continuous_iff_continuousAt.mpr (fun t =>
        (activation_product_prior_hasDerivAt (gridWindowCount d k) t ξ).continuousAt)).measurable
    have h_grid_full_score_energy_joint_measurable : Measurable (fun z : ℝ × (Fin n → Covariate d) =>
        gridFullScoreEnergy d k n P.a (P.v - η ^ 2 * z.1) η ξ z.2) := by
      let f : (ℝ × (Fin n → Covariate d)) →
          (Fin (gridWindowCount d k) → Fin 3) → Fin n → ℝ :=
        fun z => latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n z.2)
      have hV : Measurable (fun z : ℝ × (Fin n → Covariate d) => P.v - η ^ 2 * z.1) := by fun_prop
      have hf (ξ' : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) :
          Measurable (fun z => f z ξ' i) := by
        have hDesign : Measurable (fun z : ℝ × (Fin n → Covariate d) => z.2 i) :=
          (measurable_pi_apply i).comp measurable_snd
        have hComp := (indexedGridField_continuous d k η ξ').measurable.comp hDesign
        simpa only [f, grid_latent_regression_eq, Function.comp_def] using hComp
      have hq (ξ' : Fin (gridWindowCount d k) → Fin 3) (i : Fin n) (y : Fin 3) :
          Measurable (fun z => ternaryMass P.a (f z ξ' i) (P.v - η ^ 2 * z.1) y) := by
        have hPair := (hf ξ' i).prodMk hV
        have hComp := (ternaryMass_joint_continuous P.a y).measurable.comp hPair
        exact hComp
      have hL (ξ' : Fin (gridWindowCount d k) → Fin 3) (y : Fin n → Fin 3) :
          Measurable (fun z => finiteResponseLikelihood (gridWindowCount d k) n P.a
            (P.v - η ^ 2 * z.1) (f z) ξ' y) :=
        Finset.measurable_prod _ (fun i _ => hq ξ' i (y i))
      have hU (y : Fin n → Fin 3) (i : Fin n) :
          Measurable (fun z => finiteResponseVarianceTerm (gridWindowCount d k) n P.a
            (P.v - η ^ 2 * z.1) (f z) ξ y i) :=
        (Finset.measurable_prod _ (fun l _ => hq ξ l (y l))).const_mul _
      have hD (y : Fin n → Fin 3) (j : Fin (gridWindowCount d k)) :
          Measurable (fun z => latentDifference (gridWindowCount d k) j
            (fun ξ' => finiteResponseLikelihood (gridWindowCount d k) n P.a
              (P.v - η ^ 2 * z.1) (f z) ξ' y) ξ) :=
        (((hL (Function.update ξ j 2) y).const_mul (1 / 2)).add
          ((hL (Function.update ξ j 0) y).const_mul (1 / 2))).sub (hL (Function.update ξ j 1) y)
      have hR (y : Fin n → Fin 3) :
          Measurable (fun z => finiteExperimentScore (gridWindowCount d k) n P.a
            (P.v - η ^ 2 * z.1) η (f z) ξ y) :=
        ((Finset.measurable_sum _ (fun j _ => hD y j)).sub
          ((Finset.measurable_sum _ (fun i _ => hU y i)).const_mul (η ^ 2))).div (hL ξ y)
      exact Finset.measurable_sum _ (fun y _ => (hL ξ y).mul ((hR y).pow_const 2))
    have hInt := h_grid_full_score_energy_joint_measurable.stronglyMeasurable.integral_prod_right'
      (ν := Measure.pi (fun _ : Fin n => cubeVolume d))
    exact hPrior.mul hInt.measurable
  have hMeas : Measurable (fun t => Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) :=
    Real.continuous_sqrt.measurable.comp h_grid_prior_score_energy_path_measurable
  apply IntegrableOn.intervalIntegrable
  simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using (by apply Integrable.of_bound hMeas.aestronglyMeasurable (Real.sqrt (gridUniformScoreBudget P k n η)); filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht; rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]; exact Real.sqrt_le_sqrt (grid_prior_score_energy_bound C P k n η t hk hη ht hfield hvariance hmean))
abbrev LowMixtureMarks (m n : ℕ) := (Fin m → Fin 3) × (Fin n → Fin 3)
def lowMixtureWeight  (m n ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (x : α)
    (z : LowMixtureMarks m n) : ℝ :=
  activationProductPrior m t z.1 * finiteResponseLikelihood m n a V (f x) z.1 z.2
theorem lowMixtureWeight_measurable  [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (z : LowMixtureMarks m n) :
    Measurable (fun x => lowMixtureWeight m n a V t f x z) := by
  exact (Finset.measurable_prod _ (fun i _ =>
    ternaryMass_measurable_comp a V _ (hf z.1 i) (z.2 i))).const_mul _
def lowMixtureIndexKernel  [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) : Kernel α (LowMixtureMarks m n) where
  toFun x := ∑ z : LowMixtureMarks m n,
    ENNReal.ofReal (lowMixtureWeight m n a V t f x z) • Measure.dirac z
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]
    exact Finset.measurable_sum _ (fun z _ =>
      (ENNReal.measurable_ofReal.comp (lowMixtureWeight_measurable m n a V t f hf z)).mul_const _)
theorem lowMixtureIndexKernel_apply  [MeasurableSpace α]
    (m n a V t f)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (x : α) :
    lowMixtureIndexKernel m n a V t f hf x =
      ∑ z : LowMixtureMarks m n,
        ENNReal.ofReal (lowMixtureWeight m n a V t f x z) • Measure.dirac z := rfl
theorem lowMixtureWeight_nonneg {α : Type*} (m n : ℕ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y) (x : α) (z : LowMixtureMarks m n) :
    0 ≤ lowMixtureWeight m n a V t f x z :=
  have h_finite_experiment_joint_nonnegative (f) (ht : 0 ≤ t) (ht1 : t ≤ 1) (hresponse : ∀ ξ i y, 0 ≤ ternaryMass a (f ξ i) V y) : ∀ ξ y, 0 ≤ activationProductPrior m t ξ * finiteResponseLikelihood m n a V f ξ y := by
    intro ξ y
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun j _ => activation_prior_nonnegative t ht ht1 (ξ j))
    · exact Finset.prod_nonneg (fun i _ => hresponse ξ i (y i))
  (h_finite_experiment_joint_nonnegative (f x) ht.1 ht.2 (hp x)) z.1 z.2
theorem lowMixtureIndexKernel_markov  [MeasurableSpace α]
    (m n : ℕ) (a V t : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y) :
    IsMarkovKernel (lowMixtureIndexKernel m n a V t f hf) := by
  constructor
  intro x
  constructor
  simp only [lowMixtureIndexKernel_apply, Measure.finsetSum_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ =>
    lowMixtureWeight_nonneg m n a V t f ht hp x z)]
  simp only [lowMixtureWeight, Fintype.sum_prod_type]
  have h_finite_experiment_joint_normalized : ∑ ξ : Fin m → Fin 3, ∑ y : Fin n → Fin 3,
      activationProductPrior m t ξ * finiteResponseLikelihood m n a V (f x) ξ y = 1 := by
    simp_rw [← Finset.mul_sum, finite_response_normalized m n a V (f x) _ ha, mul_one]
    exact activation_product_prior_normalized m t
  rw [h_finite_experiment_joint_normalized]
  simp
theorem lowMixtureIndexKernel_integral  [MeasurableSpace α]
    (m n a V t f)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i))
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (x : α) (H : LowMixtureMarks m n → ℝ) :
    (∫ z, H z ∂lowMixtureIndexKernel m n a V t f hf x) =
      ∑ ξ, activationProductPrior m t ξ *
        ∑ y, finiteResponseLikelihood m n a V (f x) ξ y * H (ξ, y) := by
  rw [lowMixtureIndexKernel_apply, integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul,
      lowMixtureWeight, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro ξ hξ
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    have hpos : 0 ≤ activationProductPrior m t ξ * finiteResponseLikelihood m n a V (f x) ξ y :=
      lowMixtureWeight_nonneg m n a V t f ht hp x (ξ, y)
    rw [ENNReal.toReal_ofReal hpos]
    ring
  · intro z hz
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
def lowMixtureLaw  [MeasurableSpace α]
    (μ : Measure α) (m n ) (a V t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) : Measure (α × LowMixtureMarks m n) :=
  μ.compProd (lowMixtureIndexKernel m n a V t f hf)
theorem lowMixtureLaw_probability  [MeasurableSpace α]
    (μ ) [IsProbabilityMeasure μ] (m n a V t)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y) :
    IsProbabilityMeasure (lowMixtureLaw μ m n a V t f hf) := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht hp
  unfold lowMixtureLaw
  infer_instance
theorem lowMixtureLaw_integrable_of_weighted_norm  [MeasurableSpace α]
    (μ ) [IsProbabilityMeasure μ] (m n a V t)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (H : α × LowMixtureMarks m n → ℝ) (hH : Measurable H)
    (hNorm : Integrable (fun x => ∑ ξ, activationProductPrior m t ξ *
      ∑ y, finiteResponseLikelihood m n a V (f x) ξ y * |H (x, ξ, y)|) μ) :
    Integrable H (lowMixtureLaw μ m n a V t f hf) := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht hp
  apply (Measure.integrable_compProd_iff hH.aestronglyMeasurable).mpr
  constructor
  · exact Eventually.of_forall (fun x => Integrable.of_finite)
  · simp_rw [lowMixtureIndexKernel_integral m n a V t f hf ht hp,
      Real.norm_eq_abs]
    exact hNorm
theorem lowMixtureLaw_integral  [MeasurableSpace α]
    (μ ) [IsProbabilityMeasure μ] (m n a V t)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (H : α × LowMixtureMarks m n → ℝ)
    (hH : Integrable H (lowMixtureLaw μ m n a V t f hf)) :
    (∫ z, H z ∂lowMixtureLaw μ m n a V t f hf) =
      ∫ x, ∑ ξ, activationProductPrior m t ξ *
        ∑ y, finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y) ∂μ := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht hp
  rw [lowMixtureLaw, Measure.integral_compProd hH]
  simp_rw [lowMixtureIndexKernel_integral m n a V t f hf ht hp]
theorem finiteResponseLikelihood_measurable_comp  [MeasurableSpace α]
    (m n : ℕ) (a V : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i))
    (ξ : Fin m → Fin 3) (y : Fin n → Fin 3) :
    Measurable (fun x => finiteResponseLikelihood m n a V (f x) ξ y) := by
  exact Finset.measurable_prod _ (fun i _ =>
    ternaryMass_measurable_comp a V _ (hf ξ i) (y i))
def lowMixtureScore  (m n ) (a V η : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (z : α × LowMixtureMarks m n) : ℝ :=
  finiteExperimentScore m n a V η (f z.1) z.2.1 z.2.2
theorem lowMixtureScore_measurable  [MeasurableSpace α]
    (m n : ℕ) (a V η : ℝ) (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) :
    Measurable (lowMixtureScore m n a V η f) := by
  apply measurable_from_prod_countable_left
  intro z
  have hL := finiteResponseLikelihood_measurable_comp m n a V f hf
  have hU (i : Fin n) : Measurable (fun x =>
      finiteResponseVarianceTerm m n a V (f x) z.1 z.2 i) := by
    exact (Finset.measurable_prod _ (fun l _ =>
      ternaryMass_measurable_comp a V _ (hf z.1 l) (z.2 l))).const_mul _
  have hD (j : Fin m) : Measurable (fun x => latentDifference m j
      (fun ξ' => finiteResponseLikelihood m n a V (f x) ξ' z.2) z.1) := by
    exact (((hL (Function.update z.1 j 2) z.2).const_mul (1 / 2)).add
      ((hL (Function.update z.1 j 0) z.2).const_mul (1 / 2))).sub
        (hL (Function.update z.1 j 1) z.2)
  exact ((Finset.measurable_sum _ (fun j _ => hD j)).sub
    ((Finset.measurable_sum _ (fun i _ => hU i)).const_mul (η ^ 2))).div (hL z.1 z.2)
def lowMixtureConditionalScoreEnergy  (m n ) (a V η t : ℝ)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ) (x : α) : ℝ :=
  ∑ ξ, activationProductPrior m t ξ * ∑ y,
    finiteResponseLikelihood m n a V (f x) ξ y *
      finiteExperimentScore m n a V η (f x) ξ y ^ 2
theorem lowMixtureScore_sq_integrable  [MeasurableSpace α]
    (μ ) [IsProbabilityMeasure μ] (m n a V η t)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (hE : Integrable (lowMixtureConditionalScoreEnergy m n a V η t f) μ) :
    Integrable (fun z => lowMixtureScore m n a V η f z ^ 2)
      (lowMixtureLaw μ m n a V t f hf) := by
  apply lowMixtureLaw_integrable_of_weighted_norm μ m n a V t f hf ha ht hp _
    ((lowMixtureScore_measurable m n a V η f hf).pow_const 2)
  have heq : (fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
      finiteResponseLikelihood m n a V (f x) ξ y *
        |lowMixtureScore m n a V η f (x, ξ, y) ^ 2|) =
      lowMixtureConditionalScoreEnergy m n a V η t f := by
    funext x
    apply Finset.sum_congr rfl
    intro ξ hξ
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    rw [abs_of_nonneg (sq_nonneg _)]
    rfl
  rw [heq]
  exact hE
theorem lowMixtureScore_memLp_two  [MeasurableSpace α]
    (μ ) [IsProbabilityMeasure μ] (m n a V η t)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (hE : Integrable (lowMixtureConditionalScoreEnergy m n a V η t f) μ) :
    MemLp (lowMixtureScore m n a V η f) 2 (lowMixtureLaw μ m n a V t f hf) :=
  (memLp_two_iff_integrable_sq (lowMixtureScore_measurable m n a V η f hf).aestronglyMeasurable).mpr
    (lowMixtureScore_sq_integrable μ m n a V η t f hf ha ht hp hE)
theorem lowMixtureScore_centered  [MeasurableSpace α]
    (μ ) [IsProbabilityMeasure μ] (m n a V η t)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 < ternaryMass a (f x ξ i) V y)
    (hE : Integrable (lowMixtureConditionalScoreEnergy m n a V η t f) μ) :
    (∫ z, lowMixtureScore m n a V η f z ∂lowMixtureLaw μ m n a V t f hf) = 0 := by
  let := lowMixtureIndexKernel_markov m n a V t f hf ha ht (fun x ξ i y => (hp x ξ i y).le)
  let := lowMixtureLaw_probability μ m n a V t f hf ha ht (fun x ξ i y => (hp x ξ i y).le)
  have hi := (lowMixtureScore_memLp_two μ m n a V η t f hf ha ht
    (fun x ξ i y => (hp x ξ i y).le) hE).integrable (by norm_num)
  have h_lowMixtureIndexKernel_score_centered (x : α) : (∫ z, lowMixtureScore m n a V η f (x, z)
      ∂lowMixtureIndexKernel m n a V t f hf x) = 0 := by
    rw [lowMixtureIndexKernel_integral m n a V t f hf ht
      (fun x ξ i y => (hp x ξ i y).le)]
    unfold lowMixtureScore
    have hc (ξ : Fin m → Fin 3) := finite_experiment_score_centered m n a V η (f x) ξ ha
      (fun y => Finset.prod_pos (fun i _ => hp x ξ i (y i)))
    simp_rw [hc, mul_zero]
    simp
  rw [lowMixtureLaw, Measure.integral_compProd hi]
  simp_rw [h_lowMixtureIndexKernel_score_centered]
  simp
theorem lowMixtureLaw_integral_sum  [MeasurableSpace α]
    (μ ) [IsProbabilityMeasure μ] (m n a V t f)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (H : α × LowMixtureMarks m n → ℝ)
    (hH : Integrable H (lowMixtureLaw μ m n a V t f hf))
    (hξ : ∀ ξ, Integrable (fun x => ∑ y,
      finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y)) μ) :
    (∫ z, H z ∂lowMixtureLaw μ m n a V t f hf) =
      ∑ ξ, activationProductPrior m t ξ *
        ∫ x, ∑ y, finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y) ∂μ := by
  rw [lowMixtureLaw_integral μ m n a V t f hf ha ht hp H hH,
    integral_finsetSum _ (fun ξ _ => (hξ ξ).const_mul _)]
  simp_rw [integral_const_mul]
theorem lowMixtureLaw_nonneg_integral_sum  [MeasurableSpace α]
    (μ ) [IsProbabilityMeasure μ] (m n a V t f)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (H : α × LowMixtureMarks m n → ℝ) (hH : Measurable H) (hnonneg : ∀ z, 0 ≤ H z)
    (hξ : ∀ ξ, Integrable (fun x => ∑ y,
      finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y)) μ) :
    (∫ z, H z ∂lowMixtureLaw μ m n a V t f hf) =
      ∑ ξ, activationProductPrior m t ξ *
        ∫ x, ∑ y, finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y) ∂μ := by
  have heq : (fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
      finiteResponseLikelihood m n a V (f x) ξ y * |H (x, ξ, y)|) =
      (fun x => ∑ ξ, activationProductPrior m t ξ * ∑ y,
        finiteResponseLikelihood m n a V (f x) ξ y * H (x, ξ, y)) := by
    funext x
    apply Finset.sum_congr rfl
    intro ξ hξ
    congr 1
    apply Finset.sum_congr rfl
    intro y hy
    rw [abs_of_nonneg (hnonneg (x, ξ, y))]
  exact lowMixtureLaw_integral_sum μ m n a V t f hf ha ht hp H
    (lowMixtureLaw_integrable_of_weighted_norm μ m n a V t f hf ha ht hp H hH (by rw [heq]; exact integrable_finsetSum _ (fun ξ _ => (hξ ξ).const_mul _))) hξ
theorem lowMixtureScore_sq_integral_eq_sum  [MeasurableSpace α]
    (μ ) [IsProbabilityMeasure μ] (m n a V η t)
    (f : α → (Fin m → Fin 3) → Fin n → ℝ)
    (hf : ∀ ξ i, Measurable (fun x => f x ξ i)) (ha : a ≠ 0)
    (ht : t ∈ Icc (0 : ℝ) 1) (hp : ∀ x ξ i y, 0 ≤ ternaryMass a (f x ξ i) V y)
    (hξ : ∀ ξ, Integrable (fun x => ∑ y, finiteResponseLikelihood m n a V (f x) ξ y *
      finiteExperimentScore m n a V η (f x) ξ y ^ 2) μ) :
    (∫ z, lowMixtureScore m n a V η f z ^ 2 ∂lowMixtureLaw μ m n a V t f hf) =
      ∑ ξ, activationProductPrior m t ξ * ∫ x,
        ∑ y, finiteResponseLikelihood m n a V (f x) ξ y *
          finiteExperimentScore m n a V η (f x) ξ y ^ 2 ∂μ := by
  apply lowMixtureLaw_integral_sum μ m n a V t f hf ha ht hp _
    (lowMixtureScore_sq_integrable μ m n a V η t f hf ha ht hp
      (integrable_finsetSum _ (fun ξ _ => (hξ ξ).const_mul _)))
  exact hξ
theorem gridSampleField_coordinate_measurable (d k n η ξ i) :
    Measurable (fun x => gridSampleField d k n η x ξ i) :=
  (measurable_pi_apply i).comp ((measurable_pi_apply ξ).comp
    (gridSampleField_measurable d k n η))
def gridMixtureLaw (d k n ) (a v η t : ℝ) :
    Measure ((Fin n → Covariate d) × LowMixtureMarks (gridWindowCount d k) n) :=
  lowMixtureLaw (Measure.pi (fun _ => cubeVolume d)) (gridWindowCount d k) n
    a (v - η ^ 2 * t) t (gridSampleField d k n η)
    (gridSampleField_coordinate_measurable d k n η)
def gridMixtureScore (d k n ) (a v η t : ℝ) :
    (Fin n → Covariate d) × LowMixtureMarks (gridWindowCount d k) n → ℝ :=
  lowMixtureScore (gridWindowCount d k) n a (v - η ^ 2 * t) η (gridSampleField d k n η)
def gridLiftedObservable  (k ) (a : ℝ) (T : Estimator d n) :
    (Fin n → Covariate d) × LowMixtureMarks (gridWindowCount d k) n → ℝ :=
  fun z => T.val (encodeDesignResponse a (z.1, z.2.2))
theorem gridLiftedObservable_measurable  (k a)
    (T : Estimator d n) : Measurable (gridLiftedObservable k a T) :=
  (T.property.comp (encodeDesignResponse_measurable a)).comp
    (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
theorem gridSampleField_eq_latent (d k n η x) :
    gridSampleField d k n η x =
      latentRegression (gridWindowCount d k) n η (fun _ => 0) (gridSampleWeights d k n x) := by
  funext ξ i
  exact (grid_latent_regression_eq d k n η x ξ i).symm
theorem gridMixtureConditionalEnergy_integrable  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    Integrable (lowMixtureConditionalScoreEnergy (gridWindowCount d k) n P.a
      (P.v - η ^ 2 * t) η t (gridSampleField d k n η))
      (Measure.pi (fun _ : Fin n => cubeVolume d)) := by
  unfold lowMixtureConditionalScoreEnergy
  have hξ (ξ : Fin (gridWindowCount d k) → Fin 3) :=
    (grid_full_score_energy_integrable C P k n η t ξ hη ht hfield hvariance).const_mul
      (activationProductPrior (gridWindowCount d k) t ξ)
  dsimp only [gridFullScoreEnergy] at hξ
  simpa only [gridFullScoreEnergy,
    LowSmoothnessTernaryConstants.variancePath, gridSampleField_eq_latent] using
    integrable_finsetSum (Finset.univ : Finset (Fin (gridWindowCount d k) → Fin 3)) (fun ξ _ => hξ ξ)
theorem grid_mixture_score_centered  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    (∫ z, gridMixtureScore d k n P.a P.v η t z
      ∂gridMixtureLaw d k n P.a P.v η t) = 0 := by
  let _ := cubeVolume_isProbability d
  exact lowMixtureScore_centered _ _ _ _ _ _ _ _ _ P.a_pos.ne' ht
    (fun x ξ i y => grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y)
    (gridMixtureConditionalEnergy_integrable C P k n η t hη ht hfield hvariance)
theorem grid_mixture_score_energy  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k n : ℕ) (η t : ℝ)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) :
    (∫ z, (gridMixtureScore d k n P.a P.v η t z) ^ 2
      ∂gridMixtureLaw d k n P.a P.v η t) = gridPriorScoreEnergy d k n P.a P.v η t := by
  let _ := cubeVolume_isProbability d
  have hξ (ξ : Fin (gridWindowCount d k) → Fin 3) :=
    grid_full_score_energy_integrable C P k n η t ξ hη ht hfield hvariance
  simpa only [gridMixtureScore, gridMixtureLaw, gridPriorScoreEnergy,
    gridFullScoreEnergy, LowSmoothnessTernaryConstants.variancePath,
    gridSampleField_eq_latent] using lowMixtureScore_sq_integral_eq_sum
      (Measure.pi (fun _ => cubeVolume d)) (gridWindowCount d k) n
      P.a (P.v - η ^ 2 * t) η t (gridSampleField d k n η)
      (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
      (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le)
      (fun ξ => (hξ ξ).congr (Filter.Eventually.of_forall (fun x => by
        simp only [gridFullScoreEnergy, LowSmoothnessTernaryConstants.variancePath,
          gridSampleField_eq_latent])))
def gridStateRisk  (k ) (a v η t : ℝ) (T : Estimator d n)
    (ξ : Fin (gridWindowCount d k) → Fin 3) (x : Fin n → Covariate d) : ℝ :=
  ∑ y : Fin n → Fin 3, finiteResponseLikelihood (gridWindowCount d k) n a
    (v - η ^ 2 * t) (gridSampleField d k n η x) ξ y *
      (T.val (encodeDesignResponse a (x, y)) - (v - η ^ 2 * t)) ^ 2
theorem grid_state_risk_integrable  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k η t)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (T : BoundedEstimator C n) (ξ ) :
    Integrable (gridStateRisk k P.a P.v η t T.val ξ)
      (Measure.pi (fun _ => cubeVolume d)) := by
  let _ := cubeVolume_isProbability d
  let V := P.v - η ^ 2 * t
  let B := (effectiveVarianceUpper C + |V|) ^ 2
  have hp (x : Fin n → Covariate d) (y : Fin n → Fin 3) :
      0 ≤ finiteResponseLikelihood (gridWindowCount d k) n P.a V
        (gridSampleField d k n η x) ξ y :=
    (grid_response_likelihood_pos C P k n η t hη ht hfield hvariance x ξ y).le
  have hb (z : Fin n → Observation d) : (T.val.val z - V) ^ 2 ≤ B := by
    have hab : |T.val.val z| ≤ effectiveVarianceUpper C := by
      rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property z).1)]
      exact (T.property z).2
    have he := (abs_sub (T.val.val z) V).trans (add_le_add hab (le_refl |V|))
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) he 2
  have hm : Measurable (gridStateRisk k P.a P.v η t T.val ξ) := by
    apply Finset.measurable_sum
    intro y _
    exact (finiteResponseLikelihood_measurable_comp _ _ _ _ _
      (gridSampleField_coordinate_measurable d k n η) ξ y).mul
      (((T.val.property.comp (encodeDesignResponse_measurable P.a)).comp
        (measurable_id.prodMk measurable_const)).sub_const V |>.pow_const 2)
  apply (integrable_const B).mono' hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hnn : 0 ≤ gridStateRisk k P.a P.v η t T.val ξ x :=
    Finset.sum_nonneg (fun y _ => mul_nonneg (hp x y) (sq_nonneg _))
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  calc
    _ ≤ ∑ y : Fin n → Fin 3, finiteResponseLikelihood (gridWindowCount d k) n P.a V
      (gridSampleField d k n η x) ξ y * B :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hb _) (hp x y))
    _ = B := by
      rw [← Finset.sum_mul, finite_response_normalized _ _ _ _ _ _ P.a_pos.ne', one_mul]
theorem grid_mixture_risk_le_original_worstCase  (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η b t : ℝ)
    (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b)
    (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : ((2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)) * b ≤ C.holderBound)
    (T : BoundedEstimator C n) :
    (∫ z, (gridLiftedObservable k P.a T.val z - (P.v - η ^ 2 * t)) ^ 2
      ∂gridMixtureLaw d k n P.a P.v η t) ≤ (worstCaseRisk C T.val).toReal := by
  let _ := cubeVolume_isProbability d
  have hξ (ξ : Fin (gridWindowCount d k) → Fin 3) :=
    grid_state_risk_integrable C P k η t hη ht hfield hvariance T ξ
  unfold gridMixtureLaw
  rw [lowMixtureLaw_nonneg_integral_sum
    (Measure.pi (fun _ : Fin n => cubeVolume d)) (gridWindowCount d k) n
    P.a (P.v - η ^ 2 * t) t (gridSampleField d k n η)
    (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
    (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le)
    _ ((gridLiftedObservable_measurable k P.a T.val).sub_const _ |>.pow_const 2)
    (fun _ => sq_nonneg _) hξ]
  calc
    _ ≤ ∑ ξ : Fin (gridWindowCount d k) → Fin 3,
      activationProductPrior (gridWindowCount d k) t ξ * (worstCaseRisk C T.val).toReal := by
      apply Finset.sum_le_sum
      intro ξ _
      apply mul_le_mul_of_nonneg_left
      · apply (ENNReal.ofReal_le_iff_le_toReal (boundedEstimator_worstCaseRisk_ne_top C T)).mp
        have h_gridPathParameter_finite_risk_le_worstCase : ENNReal.ofReal (∫ x, ∑ y : Fin n → Fin 3,
            finiteResponseLikelihood (gridWindowCount d k) n P.a (P.v - η ^ 2 * t)
              (fun ξ i => indexedGridField d k η ξ (x i)) ξ y *
              (T.val.val (encodeDesignResponse P.a (x, y)) - (P.v - η ^ 2 * t)) ^ 2
            ∂Measure.pi (fun _ : Fin n => cubeVolume d)) ≤ worstCaseRisk C T.val := by
          have hB (z : Fin n → Observation d) : |T.val.val z| ≤ effectiveVarianceUpper C := by
            rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property z).1)]
            exact (T.property z).2
          rw [gridPathParameter_risk_formula C P k η t ξ hη ht hfield hvariance T.val _ hB]
          have h_gridPathParameter_admissible : Admissible C (gridPathParameter C P k η t ξ hη ht hfield hvariance) := by
            have ho  := C.order_lt.trans_le hs1
            have : C.order < 1 := by exact_mod_cast ho
            apply P.pathParameter_admissible_order_zero _ _ η t ht hvariance _ (by omega)
              (↑2 ^ d * b) ((68 * ↑2 ^ d * (d + 1)) * b)
              (by positivity) (by positivity) (by nlinarith [hholder])
            · intro x
              exact (indexedGridField_abs_bound d k η hη ξ x).trans (mul_le_mul_of_nonneg_left (by rw [hscale]; exact div_le_self hb (Real.one_le_rpow (by exact_mod_cast hk) C.smoothness_pos.le)) (by positivity))
            · intro x y
              rw [hscale, indexedGridField_eq]
              have h_gridPriorField_holder_bound (ξ : (Fin d → Fin (k + 1)) → Fin 3) : |gridPriorField d k (b / ↑k ^ C.smoothness) ξ x - gridPriorField d k (b / ↑k ^ C.smoothness) ξ y| ≤
                  68 * ↑2 ^ d * (d + 1) * b * euclideanNorm (x - y) ^ C.smoothness := by
                have hkp : 0 < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
                have hη : 0 ≤ b / (k : ℝ) ^ C.smoothness := by positivity
                have h_scaled_lipschitz_holder_bound (A : ℝ) (r : ℝ) (u : ℝ) (hA : 0 ≤ A) (hr : 0 ≤ r) (hbounded : u ≤ A * (b / k ^ C.smoothness)) (hlip : u ≤ A * (b / k ^ C.smoothness) * k * r) : u ≤ A * b * r ^ C.smoothness := by
                  have hcoef : 0 ≤ A * (b / k ^ C.smoothness) := by positivity
                  have heq : A * (b / k ^ C.smoothness) * (k * r) ^ C.smoothness = A * b * r ^ C.smoothness := by
                    rw [Real.mul_rpow hkp.le hr]
                    field_simp
                  by_cases hkr : k * r ≤ 1
                  · have hsmall := Real.self_le_rpow_of_le_one (mul_nonneg hkp.le hr) hkr hs1
                    calc
                      u ≤ A * (b / k ^ C.smoothness) * (k * r) := by nlinarith [hlip]
                      _ ≤ A * (b / k ^ C.smoothness) * (k * r) ^ C.smoothness := mul_le_mul_of_nonneg_left hsmall hcoef
                      _ = _ := heq
                  · have := Real.one_le_rpow (le_of_lt (lt_of_not_ge hkr)) C.smoothness_pos.le
                    calc
                      u ≤ A * (b / k ^ C.smoothness) := hbounded
                      _ ≤ A * (b / k ^ C.smoothness) * (k * r) ^ C.smoothness := by nlinarith
                      _ = _ := heq
                apply h_scaled_lipschitz_holder_bound (68 * (2 : ℝ) ^ d * (d + 1)) _ _ (by positivity) (Real.sqrt_nonneg _)
                · have := gridPriorField_abs_bound d k _ hη ξ x
                  have := gridPriorField_abs_bound d k _ hη ξ y
                  have : |gridPriorField d k (b / ↑k ^ C.smoothness) ξ x -
                      gridPriorField d k (b / ↑k ^ C.smoothness) ξ y| ≤
                        |gridPriorField d k (b / ↑k ^ C.smoothness) ξ x| + |gridPriorField d k (b / ↑k ^ C.smoothness) ξ y| :=
                    by
                      simpa only [sub_zero, zero_sub, abs_neg] using (abs_sub_le
                        (gridPriorField d k (b / ↑k ^ C.smoothness) ξ x) 0 (gridPriorField d k (b / ↑k ^ C.smoothness) ξ y))
                  nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℝ) ^ d) hη]
                · exact gridPriorField_lipschitz_bound d k _ hη ξ x y
              exact h_gridPriorField_holder_bound _
          exact le_iSup (fun θ : {θ // Admissible C θ} => meanSquaredRisk T.val θ.val)
            ⟨_, h_gridPathParameter_admissible⟩
        exact h_gridPathParameter_finite_risk_le_worstCase
      · exact Finset.prod_nonneg (fun j _ => activation_prior_nonnegative t ht.1 ht.2 (ξ j))
    _ = _ := by rw [← Finset.sum_mul, activation_product_prior_normalized, one_mul]
def gridEncodedObservable  (a : ℝ) (T : Estimator d n) :
    (Fin n → Covariate d) → (Fin n → Fin 3) → ℝ :=
  fun x y => T.val (encodeDesignResponse a (x, y))
theorem grid_prior_minimax_lower {d n : ℕ} (C : ModelConstants d)
    (P : LowSmoothnessTernaryConstants C) (k : ℕ) (η b : ℝ)
    (hk : 1 ≤ k) (hs1 : C.smoothness ≤ 1) (hb : 0 ≤ b) (hη : 0 ≤ η)
    (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ)
    (hscale : η = b / (k : ℝ) ^ C.smoothness)
    (hholder : ((2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)) * b ≤ C.holderBound)
    (hmean : n * (2 / (k : ℝ)) ^ d ≤ 1) (hbudget : gridUniformScoreBudget P k n η ≤ 1) :
    ENNReal.ofReal (η ^ 2 / 3) ≤ minimaxRMS C n := by
  have h_grid_mixture_probability (t : ℝ) (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) : IsProbabilityMeasure (gridMixtureLaw d k n P.a P.v η t) := by
    let _ := cubeVolume_isProbability d
    exact lowMixtureLaw_probability _ _ _ _ _ _ _ _ P.a_pos.ne' ht
      (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le)
  have h_grid_mixture_score_memLp (t : ℝ) (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) : MemLp (gridMixtureScore d k n P.a P.v η t) 2
      (gridMixtureLaw d k n P.a P.v η t) := by
    let _ := cubeVolume_isProbability d
    exact lowMixtureScore_memLp_two _ _ _ _ _ _ _ _ _ P.a_pos.ne' ht
      (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le)
      (gridMixtureConditionalEnergy_integrable C P k n η t hη ht hfield hvariance)
  have h_grid_lifted_observable_memLp (t) (hη : 0 ≤ η) (ht : t ∈ Icc (0 : ℝ) 1) (hfield : ((2 : ℝ) ^ d + 2) * η ≤ P.ρ) (hvariance : η ^ 2 ≤ P.ρ) (T : BoundedEstimator C n) : MemLp (gridLiftedObservable k P.a T.val) 2 (gridMixtureLaw d k n P.a P.v η t) := by
    let _ := h_grid_mixture_probability t hη ht hfield hvariance
    apply MemLp.of_bound (gridLiftedObservable_measurable k P.a T.val).aestronglyMeasurable
      (effectiveVarianceUpper C)
    apply Filter.Eventually.of_forall
    intro z
    change |T.val.val (encodeDesignResponse P.a (z.1, z.2.2))| ≤ effectiveVarianceUpper C
    rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property _).1)]
    exact (T.property _).2
  have hnonneg : 0 ≤ η ^ 2 / 3 := by positivity
  have hlower : ENNReal.ofReal (η ^ 2 / 3) ^ 2 ≤ minimaxRisk C n := by
    rw [minimaxRisk_eq_inf_bounded C n]
    apply le_iInf
    intro T
    rw [← ENNReal.ofReal_pow hnonneg 2]
    apply (ENNReal.ofReal_le_iff_le_toReal (boundedEstimator_worstCaseRisk_ne_top C T)).mpr
    have h_grid_prior_boundedEstimator_separation : η ^ 2 ≤ 3 * Real.sqrt ((worstCaseRisk C T.val).toReal) := by
      let r := Real.sqrt ((worstCaseRisk C T.val).toReal)
      let m := fun t => gridMixtureExpectation d k n P.a P.v η t (gridEncodedObservable P.a T.val)
      let m' := fun t => ∫ x,
        gridMixtureScoreObservable d k n P.a P.v η t (gridEncodedObservable P.a T.val) x
        ∂Measure.pi (fun _ : Fin n => cubeVolume d)
      have hr : 0 ≤ r := Real.sqrt_nonneg _
      have h_gridEncodedObservable_measurable : Measurable (gridEncodedObservable P.a T.val) := by
        apply Measurable.of_eval
        intro y
        exact (T.val.property.comp (encodeDesignResponse_measurable P.a)).comp
          (measurable_id.prodMk measurable_const)
      have hT := h_gridEncodedObservable_measurable
      have h_gridEncodedObservable_norm_le (x) : ‖gridEncodedObservable P.a T.val x‖ ≤ effectiveVarianceUpper C := by
        apply (pi_norm_le_iff_of_nonneg (C.varianceLower_pos.le.trans (effective_variance_interval_nondegenerate C).le)).mpr
        intro y
        change |T.val.val (encodeDesignResponse P.a (x, y))| ≤ effectiveVarianceUpper C
        rw [abs_of_nonneg (C.varianceLower_pos.le.trans (T.property _).1)]
        exact (T.property _).2
      have hTB : ∀ᵐ x ∂Measure.pi (fun _ : Fin n => cubeVolume d),
          ‖gridEncodedObservable P.a T.val x‖ ≤ effectiveVarianceUpper C :=
        Filter.Eventually.of_forall h_gridEncodedObservable_norm_le
      have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : HasDerivAt m (m' t) t :=
        (grid_mixture_expectation_hasDerivAt C P k n η t (effectiveVarianceUpper C)
          hη ht hfield hvariance _ hT hTB).2
      have hderivI  :=
        grid_mixture_score_observable_intervalIntegrable C P k n η (effectiveVarianceUpper C)
          hη hfield hvariance _ hT hTB
      have hris (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
          (∫ z, (gridLiftedObservable k P.a T.val z - (P.v - η ^ 2 * t)) ^ 2
            ∂gridMixtureLaw d k n P.a P.v η t) ≤ r ^ 2 := by
        rw [Real.sq_sqrt ENNReal.toReal_nonneg]
        exact grid_mixture_risk_le_original_worstCase C P k η b t hk hs1 hb hη ht
          hfield hvariance hscale hholder T
      have hderivBound (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |m' t| ≤ r * (fun t => Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) t := by
        let _ := h_grid_mixture_probability t hη ht hfield hvariance
        have h := probability_score_bound (gridMixtureLaw d k n P.a P.v η t)
          (gridLiftedObservable k P.a T.val) (gridMixtureScore d k n P.a P.v η t)
          (P.v - η ^ 2 * t) r
          (h_grid_lifted_observable_memLp t hη ht hfield hvariance T)
          (h_grid_mixture_score_memLp t hη ht hfield hvariance) hr
          (grid_mixture_score_centered C P k n η t hη ht hfield hvariance) (hris t ht)
        have h_grid_mixture_score_observable_eq : (∫ z, gridLiftedObservable k P.a T.val z * gridMixtureScore d k n P.a P.v η t z
            ∂gridMixtureLaw d k n P.a P.v η t) =
            ∫ x, gridMixtureScoreObservable d k n P.a P.v η t (gridEncodedObservable P.a T.val) x
              ∂Measure.pi (fun _ => cubeVolume d) := by
          let _ := cubeVolume_isProbability d
          have hi := (h_grid_lifted_observable_memLp t hη ht hfield hvariance T).integrable_mul
            (h_grid_mixture_score_memLp t hη ht hfield hvariance)
          simpa only [gridLiftedObservable, gridMixtureScore, gridMixtureLaw,
            gridMixtureScoreObservable, gridEncodedObservable, lowMixtureScore, Pi.mul_apply, mul_assoc,
            LowSmoothnessTernaryConstants.variancePath, gridSampleField] using
            lowMixtureLaw_integral (Measure.pi (fun _ => cubeVolume d))
              (gridWindowCount d k) n P.a (P.v - η ^ 2 * t) t (gridSampleField d k n η)
              (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
              (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le) _ hi
        rw [h_grid_mixture_score_observable_eq,
          grid_mixture_score_energy C P k n η t hη ht hfield hvariance] at h
        exact h
      have hbias (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : |m t - (P.v - η ^ 2 * t)| ≤ r := by
        let _ := h_grid_mixture_probability t hη ht hfield hvariance
        have h := probability_mean_error_le (gridMixtureLaw d k n P.a P.v η t)
          (gridLiftedObservable k P.a T.val) (P.v - η ^ 2 * t) r
          (h_grid_lifted_observable_memLp t hη ht hfield hvariance T) hr (hris t ht)
        have h_grid_mixture_mean_eq : (∫ z, gridLiftedObservable k P.a T.val z ∂gridMixtureLaw d k n P.a P.v η t) =
            gridMixtureExpectation d k n P.a P.v η t (gridEncodedObservable P.a T.val) := by
          let _ := cubeVolume_isProbability d
          let _ := h_grid_mixture_probability t hη ht hfield hvariance
          have hi := (h_grid_lifted_observable_memLp t hη ht hfield hvariance T).integrable
            (by norm_num)
          exact lowMixtureLaw_integral (Measure.pi (fun _ => cubeVolume d))
            (gridWindowCount d k) n P.a (P.v - η ^ 2 * t) t (gridSampleField d k n η)
            (gridSampleField_coordinate_measurable d k n η) P.a_pos.ne' ht
            (fun x ξ i y => (grid_response_positive C P k n η t ξ x hη ht hfield hvariance i y).le) _ hi
        rw [h_grid_mixture_mean_eq] at h
        exact h
      have hsep := path_separation_le (by norm_num : (0 : ℝ) ≤ 1) hderiv hderivI (grid_sqrt_score_energy_intervalIntegrable C P k n η hk hη hfield hvariance hmean)
        hderivBound (hbias 0 (by norm_num)) (hbias 1 (by norm_num))
      have h_grid_sqrt_score_energy_integral_le_one : (∫ t in ↑0..1, Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) ≤ 1 := by
        have h_grid_sqrt_score_energy_integral_le : (∫ t in ↑0..1, Real.sqrt (gridPriorScoreEnergy d k n P.a P.v η t)) ≤
            Real.sqrt (gridUniformScoreBudget P k n η) := by
          have hInt := grid_sqrt_score_energy_intervalIntegrable C P k n η hk hη hfield hvariance hmean
          have h := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hInt
            (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.sqrt (gridUniformScoreBudget P k n η)) volume 0 1)
            (fun t ht => Real.sqrt_le_sqrt (grid_prior_score_energy_bound C P k n η t hk hη ht hfield hvariance hmean))
          simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, one_mul] using h
        apply h_grid_sqrt_score_energy_integral_le.trans
        simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hbudget
      have := h_grid_sqrt_score_energy_integral_le_one
      have he : |(P.v - η ^ 2 * 1) - (P.v - η ^ 2 * 0)| = η ^ 2 := by
        simp [abs_of_nonneg (sq_nonneg η)]
      rw [he] at hsep
      exact hsep.trans (mul_le_mul_of_nonneg_right (by linarith) hr)
    have := h_grid_prior_boundedEstimator_separation
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
variable {d : ℕ}
def pairGridMSEEnvelope (d : ℕ) (s x : ℝ) : ℝ :=
  1 / x + (lowSmoothnessGrid d s x ) ^ d / (x * (x - 1)) +
    (lowSmoothnessGrid d s x ) ^ (-4 * s)
theorem pairGrid_rms_of_mse_bound  
    (hs : 0 < s) (hx : 2 ≤ x) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hRisk : R ^ 2 ≤ C * pairGridMSEEnvelope d s x) :
    R ≤ Real.sqrt (C * (2 * ↑5 ^ d + 1)) *
      (x ^ (-(1 / 2 : ℝ)) + x ^ (-4 * s / (↑d + 4 * s))) := by
  have hx0 : 0 < x := by linarith
  have h_pairGridMSEEnvelope_bound : pairGridMSEEnvelope d s x ≤
      (2 * ↑5 ^ d + 1) * (1 / x + x ^ (-8 * s / (↑d + 4 * s))) := by
    have hx1 : 1 ≤ x := by linarith
    have hx0 : 0 < x := by linarith
    have : 0 < x * (x - 1) := mul_pos hx0 (by linarith)
    have hp : 0 ≤ (lowSmoothnessGrid d s x : ℝ) ^ d := by positivity
    have hfirst : (lowSmoothnessGrid d s x : ℝ) ^ d / (x * (x - 1)) ≤
        2 * ((lowSmoothnessGrid d s x : ℝ) ^ d / x ^ 2) := by
      have h_pairGrid_denominator_bound : x ^ 2 / 2 ≤ x * (x - 1) := by nlinarith
      have hh := div_le_div_of_nonneg_left hp (show 0 < x ^ 2 / 2 by positivity)
        h_pairGrid_denominator_bound
      have hid : (lowSmoothnessGrid d s x : ℝ) ^ d / (x ^ 2 / 2) =
          2 * ((lowSmoothnessGrid d s x : ℝ) ^ d / x ^ 2) := by ring
      exact hh.trans_eq hid
    have h_lowSmoothnessGrid_pair_variance_budget : (lowSmoothnessGrid d s x : ℝ) ^ d / x ^ 2 ≤
        ↑5 ^ d * x ^ (-8 * s / (↑d + 4 * s)) := by
      have hx0 : 0 < x := by linarith
      have hk := lowSmoothnessGrid_positive (d := d) hs hx1
      have hupper := pow_le_pow_left₀ hk.le (lowSmoothnessGrid_rounding (d := d) hs hx1).2 d
      rw [mul_pow, ← Real.rpow_mul_natCast hx0.le] at hupper
      have heq : lowSmoothnessGridExponent d s * d - 2 = -8 * s / (↑d + 4 * s) := by
        unfold lowSmoothnessGridExponent
        field_simp
        ring
      have hid : ↑5 ^ d * x ^ (lowSmoothnessGridExponent d s * d) / x ^ ↑2 =
          ↑5 ^ d * x ^ (-8 * s / (↑d + 4 * s)) := by
        rw [← Real.rpow_two, mul_div_assoc, ← Real.rpow_sub hx0, heq]
      rw [← hid]
      exact div_le_div_of_nonneg_right hupper (sq_nonneg x)
    have hvar := mul_le_mul_of_nonneg_left h_lowSmoothnessGrid_pair_variance_budget
      (by norm_num : (0 : ℝ) ≤ 2)
    have h_lowSmoothnessGrid_pair_bias_budget : (lowSmoothnessGrid d s x : ℝ) ^ (-4 * s) ≤ x ^ (-8 * s / (↑d + 4 * s)) := by
      have hx0 : 0 < x := by linarith
      have hbase : x ^ lowSmoothnessGridExponent d s ≤ (lowSmoothnessGrid d s x : ℝ) := by
        have hh := (lowSmoothnessGrid_rounding (d := d) hs hx1).1
        have := Real.rpow_pos_of_pos hx0 (lowSmoothnessGridExponent d s)
        linarith
      have hh := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hx0 _) hbase (by linarith : -4 * s ≤ 0)
      rw [← Real.rpow_mul hx0.le] at hh
      have heq : lowSmoothnessGridExponent d s * (-4 * s) = -8 * s / (↑d + 4 * s) := by
        unfold lowSmoothnessGridExponent
        ring
      rw [heq] at hh
      exact hh
    have hbias := h_lowSmoothnessGrid_pair_bias_budget
    have hcoef : 0 ≤ 2 * ↑5 ^ d * (1 / x) := by positivity
    unfold pairGridMSEEnvelope
    nlinarith only [hfirst, hvar, hbias, hcoef]
  have hsq := Real.sqrt_le_sqrt (hRisk.trans (mul_le_mul_of_nonneg_left h_pairGridMSEEnvelope_bound hC))
  rw [Real.sqrt_sq hR, ← mul_assoc, Real.sqrt_mul (by positivity)] at hsq
  apply hsq.trans
  have hadd : Real.sqrt (1 / x + x ^ (-8 * s / (↑d + 4 * s))) ≤
      Real.sqrt (1 / x) + Real.sqrt (x ^ (-8 * s / (↑d + 4 * s))) := by
    have hA : 0 ≤ 1 / x := by positivity
    have hB : 0 ≤ x ^ (-8 * s / (↑d + 4 * s)) := (Real.rpow_pos_of_pos hx0 _).le
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hB,
      mul_nonneg (Real.sqrt_nonneg (1 / x)) (Real.sqrt_nonneg (x ^ (-8 * s / (↑d + 4 * s))))]
  have h_sqrt_inverse_sample : Real.sqrt (1 / x) = x ^ (-(1 / 2 : ℝ)) := by
    rw [one_div, Real.sqrt_inv, Real.sqrt_eq_rpow, Real.rpow_neg hx0.le]
  have h_sqrt_pair_rate : Real.sqrt (x ^ (-8 * s / (↑d + 4 * s))) = x ^ (-4 * s / (↑d + 4 * s)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]
    congr 1
    ring
  rw [h_sqrt_inverse_sample, h_sqrt_pair_rate] at hadd
  exact mul_le_mul_of_nonneg_left hadd (Real.sqrt_nonneg _)
def elementaryDenominatorKernel  (k : ℕ) (hk : 0 < k) :
    Observation d × Observation d → ℝ := sameLabelKernel (regularObservationLabel k hk)
def elementaryNumeratorKernel  (k : ℕ) (hk : 0 < k) :
    Observation d × Observation d → ℝ :=
  pairWindowScore (regularObservationLabel k hk) Prod.snd 0
def elementaryNumerator  (n k : ℕ) (hk : 0 < k) :
    (Fin n → Observation d) → ℝ :=
  PairUStatistic.pairAverage n (elementaryNumeratorKernel k hk)
def elementaryDenominator  (n k : ℕ) (hk : 0 < k) :
    (Fin n → Observation d) → ℝ :=
  PairUStatistic.pairAverage n (elementaryDenominatorKernel k hk)
def elementaryFloor (d k : ℕ) : ℝ := 1 / (2 * ↑k ^ d)
def elementaryGridEstimator  (C : ModelConstants d) (n k : ℕ) (hk : 0 < k) :
    Estimator d n :=
  ⟨stabilizedRatio C.varianceLower C.varianceUpper (elementaryFloor d k)
      (elementaryNumerator n k hk) (elementaryDenominator n k hk),
    stabilizedRatio_measurable _ _ _
      (PairUStatistic.pairAverage_measurable n
        (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
          Prod.snd measurable_snd 0))
      (PairUStatistic.pairAverage_measurable n
        (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk)))⟩
theorem pairAverage_sub_mul {E : Type*} [MeasurableSpace E] (n : ℕ)
    (K L : E × E → ℝ) (c : ℝ) (x : Fin n → E) :
    PairUStatistic.pairAverage n (fun z => K z - c * L z) x =
      PairUStatistic.pairAverage n K x - c * PairUStatistic.pairAverage n L x := by
  unfold PairUStatistic.pairAverage
  simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
theorem elementary_score_identity  (θ : RegressionParameter d)
    (n k : ℕ) (hk : 0 < k) (z : Fin n → Observation d) :
    elementaryNumerator n k hk z - θ.variance * elementaryDenominator n k hk z =
      PairUStatistic.pairAverage n (regularPairScore θ k hk) z := by
  have he : regularPairScore θ k hk =
      (fun z => elementaryNumeratorKernel k hk z - θ.variance *
        elementaryDenominatorKernel k hk z) := by
    funext z
    unfold regularPairScore elementaryNumeratorKernel elementaryDenominatorKernel
      pairWindowScore sameLabelKernel
    split_ifs <;> ring
  rw [he, pairAverage_sub_mul]
  rfl
def elementaryRowBound  (C : ModelConstants d) : ℝ :=
  responseFourthBound C + (C.varianceUpper + responseSecondBound C) ^ 2
def elementaryKernelBound  (C : ModelConstants d) : ℝ :=
  8 * responseFourthBound C + 2 * C.varianceUpper ^ 2
theorem elementaryRowBound_pos  (C : ModelConstants d) :
    0 < elementaryRowBound C := add_pos_of_pos_of_nonneg (responseFourthBound_pos C) (sq_nonneg _)
theorem elementaryKernelBound_pos  (C : ModelConstants d) :
    0 < elementaryKernelBound C := by
  unfold elementaryKernelBound
  have := responseFourthBound_pos C
  positivity
def elementaryBiasFactor  (C : ModelConstants d) : ℝ :=
  (2 * (↑d + 1) * C.holderBound) ^ 4 * (Real.sqrt d) ^ (4 * elementarySmoothness C)
def elementaryUpperConstant  (C : ModelConstants d) : ℝ :=
  (64 * C.densityUpper ^ 2 * elementaryRowBound C +
    32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2) +
    16 * C.densityUpper * (elementaryKernelBound C + C.varianceUpper ^ 2) +
    2 * C.densityUpper ^ 2 * elementaryBiasFactor C
def elementaryChosenGrid  (C : ModelConstants d) (n : ℕ) : ℕ :=
  lowSmoothnessGrid d (elementarySmoothness C) n
theorem elementaryChosenGrid_pos {d n : ℕ} (C : ModelConstants d) (hn : 0 < n) :
    0 < elementaryChosenGrid C n := by
  have := lowSmoothnessGrid_ge_four (d := d) (elementarySmoothness_pos C)
    (show 1 ≤ ↑n by exact_mod_cast hn)
  unfold elementaryChosenGrid
  omega
def elementaryEstimator  (C : ModelConstants d) (n : ℕ) : Estimator d n :=
  if hn : 2 ≤ n then
    elementaryGridEstimator C n (elementaryChosenGrid C n)
      (elementaryChosenGrid_pos C (by omega))
  else constantEstimator d n C.varianceLower
def elementaryRMSConstant  (C : ModelConstants d) : ℝ :=
  2 * Real.sqrt (elementaryUpperConstant C * (2 * ↑5 ^ d + 1)) +
    C.varianceUpper - C.varianceLower
theorem paper_low_smoothness  (C : ModelConstants d) : LowSmoothnessClaim C := by
  have h_regularPairScore_mean_eq_signal (θ : RegressionParameter d) (hθ : Admissible C θ) (k) (hk) : (∫ z, regularPairScore θ k hk z
      ∂(observationLaw θ).prod (observationLaw θ)) =
      ∫ z, pairWindowScore (regularObservationLabel k hk)
        (fun z : Observation d => θ.regression z.1) 0 z
        ∂(observationLaw θ).prod (observationLaw θ) := by
    have h_observationLaw_covariate_integral (g : Covariate d → ℝ) (hg : Measurable g) : (∫ z, g z.1 ∂observationLaw θ) = ∫ x, g x ∂designLaw θ := by
      have hh := integral_map (μ := observationLaw θ) measurable_fst.aemeasurable
        hg.aestronglyMeasurable
      rw [(observationLaw_fst_measurePreserving C θ hθ).map_eq] at hh
      exact hh.symm
    let := observationLaw_isProbability C θ hθ
    rw [regularPairScore,
      pairWindowScore_integral (observationLaw θ) _
        (regularObservationLabel_measurable k hk) Prod.snd measurable_snd θ.variance
        (observationLaw_response_memLp_two C θ hθ),
      pairWindowScore_integral (observationLaw θ) _
        (regularObservationLabel_measurable k hk)
        (fun z : Observation d => θ.regression z.1) (hθ.2.1.comp measurable_fst) 0
        (observationLaw_regression_memLp_two C θ hθ)]
    apply Finset.sum_congr rfl
    intro c hc
    let A := (regularGridCell k hk) ⁻¹' {c}
    have hA : MeasurableSet A :=
      (measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk)
    have h_observationLaw_localized_regression_first : (∫ z, (Prod.fst ⁻¹' A).indicator (Prod.snd : Observation d → ℝ) z
        ∂observationLaw θ) =
        ∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => θ.regression z.1) z
          ∂observationLaw θ := by
      have h_observationLaw_localized_first_integral : (∫ z, (Prod.fst ⁻¹' A).indicator (Prod.snd : Observation d → ℝ) z
        ∂observationLaw θ) =
        ∫ x, A.indicator θ.regression x ∂designLaw θ := by
        let := observationLaw_isProbability C θ hθ
        have hi := (observationLaw_response_memLp_two C θ hθ).integrable (by norm_num)
        rw [observationLaw_integral_conditioning C θ hθ _
          (hi.indicator (measurable_fst hA))]
        apply integral_congr_ae
        filter_upwards [hθ.2.2.2.2.2.2.2] with x hx
        by_cases hxa : x ∈ A
        · simp [hxa, integral_add (integrable_const _) hx.1, hx.2.2.2.1]
        · simp [hxa]
      rw [h_observationLaw_localized_first_integral]
      have hh := h_observationLaw_covariate_integral (A.indicator θ.regression)
        (hθ.2.1.indicator hA)
      have heq : (fun z : Observation d => (Prod.fst ⁻¹' A).indicator
          (fun z => θ.regression z.1) z) = (fun z => A.indicator θ.regression z.1) := by
        funext z
        by_cases hz : z.1 ∈ A <;> simp [Set.indicator, hz]
      rw [heq]
      exact hh.symm
    have h_observationLaw_localized_regression_second : (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 2) z
        ∂observationLaw θ) =
        (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => θ.regression z.1 ^ 2) z
          ∂observationLaw θ) + θ.variance * (designLaw θ).real A := by
      have h_observationLaw_localized_second_integral : (∫ z, (Prod.fst ⁻¹' A).indicator (fun z : Observation d => z.2 ^ 2) z
        ∂observationLaw θ) =
        ∫ x, A.indicator (fun x => θ.regression x ^ 2 + θ.variance) x ∂designLaw θ := by
        have hi := (observationLaw_response_memLp_two C θ hθ).integrable_sq
        rw [observationLaw_integral_conditioning C θ hθ _
          (hi.indicator (measurable_fst hA))]
        apply integral_congr_ae
        filter_upwards [admissible_conditional_response_second C θ hθ] with x hx
        by_cases hxa : x ∈ A
        · simpa [hxa] using hx.2.1
        · simp [hxa]
      rw [h_observationLaw_localized_second_integral]
      have hh := h_observationLaw_covariate_integral
        (A.indicator (fun x => θ.regression x ^ 2)) ((hθ.2.1.pow_const 2).indicator hA)
      have hc : (∫ z : Observation d, (Prod.fst ⁻¹' A).indicator
          (fun z => θ.regression z.1 ^ 2) z ∂observationLaw θ) =
          ∫ x, A.indicator (fun x => θ.regression x ^ 2) x ∂designLaw θ := by
        have heq : (fun z : Observation d => (Prod.fst ⁻¹' A).indicator
            (fun z => θ.regression z.1 ^ 2) z) =
            (fun z => A.indicator (fun x => θ.regression x ^ 2) z.1) := by
          funext z
          by_cases hz : z.1 ∈ A <;> simp [Set.indicator, hz]
        rw [heq]
        exact hh
      rw [hc, integral_indicator hA, integral_indicator hA]
      let := designLaw_isProbability C θ hθ
      have h_designLaw_regression_memLp_two : MemLp θ.regression 2 (designLaw θ) := by
        let := designLaw_isProbability C θ hθ
        apply MemLp.of_bound hθ.2.1.aestronglyMeasurable C.holderBound
        filter_upwards [designLaw_cube_ae θ] with x hx
        simpa only [Real.norm_eq_abs] using admissible_regression_value_bound C θ hθ x hx
      rw [integral_add h_designLaw_regression_memLp_two.integrable_sq.restrict
          (integrable_const θ.variance), integral_const]
      simp only [measureReal_restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]
      ring
    rw [regularObservationLabel_mass C θ hθ k hk c,
      regularObservationLabel_fiber k hk c, h_observationLaw_localized_regression_first, h_observationLaw_localized_regression_second]
    dsimp [A, regularGridProbability]
    ring
  intro hs
  have h_low_smoothness_max_minimax_lower : ∃ c, 0 < c ∧ ∀ n, 1 ≤ n →
      ENNReal.ofReal (c * lowSmoothnessScale C.smoothness d n) ≤ minimaxRMS C n := by
    by_cases hd : d ≤ 4 * C.smoothness
    · obtain ⟨c, hc, hbound⟩ := parametric_minimax_lower C
      refine ⟨c, hc, ?_⟩
      intro n hn
      have h_lowSmoothnessScale_eq_root : lowSmoothnessScale C.smoothness d n = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        exact max_eq_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1 : ℝ) ≤ n) (by apply neg_le_neg; apply (le_div_iff₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith [C.smoothness_pos])).mpr; nlinarith))
      rw [h_lowSmoothnessScale_eq_root]
      exact hbound n hn
    have h_low_smoothness_nonparametric_minimax_lower (hd : 4 * C.smoothness ≤ (d : ℝ)) : ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n →
        ENNReal.ofReal (c * ↑n ^ (-4 * C.smoothness / (↑d + 4 * C.smoothness))) ≤
          minimaxRMS C n := by
      obtain ⟨P⟩ := lowSmoothnessTernaryConstants_exists C
      let M := (2 : ℝ) ^ d + 2
      let H := (2 : ℝ) ^ d + 68 * (2 : ℝ) ^ d * (d + 1)
      let Q := lowSmoothnessScoreConstant P
      have hM : 0 < M := by dsimp [M]; positivity
      have hH : 0 < H := by dsimp [H]; positivity
      have hQ  := lowSmoothnessScoreConstant_nonneg P
      let b := min (min (min (min 1 (P.ρ / M)) (Real.sqrt P.ρ)) (C.holderBound / H)) (1 / (Q + 1))
      have hb : 0 < b := lt_min
        (lt_min (lt_min (lt_min (by norm_num) (div_pos P.ρ_pos hM)) (Real.sqrt_pos.mpr P.ρ_pos))
          (div_pos C.holderBound_pos hH)) (div_pos (by norm_num) (by linarith))
      have hbQ : b ≤ 1 / (Q + 1) := min_le_right _ _
      have hbH : b ≤ C.holderBound / H := (min_le_left _ _).trans (min_le_right _ _)
      have hbS : b ≤ Real.sqrt P.ρ := ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
      have hbM : b ≤ P.ρ / M := (((min_le_left _ _).trans (min_le_left _ _)).trans
        (min_le_left _ _)).trans (min_le_right _ _)
      have hb1 : b ≤ 1 := (((min_le_left _ _).trans (min_le_left _ _)).trans
        (min_le_left _ _)).trans (min_le_left _ _)
      have hfield : M * b ≤ P.ρ := by
        have h := (le_div_iff₀ hM).mp hbM
        nlinarith
      have hvariance : b ^ 2 ≤ P.ρ := by
        nlinarith [Real.sq_sqrt P.ρ_pos.le, Real.sqrt_nonneg P.ρ]
      have hholder : H * b ≤ C.holderBound := by
        have := (le_div_iff₀ hH).mp hbH
        nlinarith
      have hb4 : b ^ 4 ≤ b := by
        calc
          _ = b ^ 3 * b := by ring
          _ ≤ 1 * b := mul_le_mul_of_nonneg_right (pow_le_one₀ (n := 3) hb.le hb1) hb.le
          _ = b := one_mul b
      have hscore : Q * b ^ 4 ≤ 1 := by
        have := (le_div_iff₀ (by linarith : 0 < Q + 1)).mp hbQ
        exact (mul_le_mul_of_nonneg_left hb4 hQ).trans (by nlinarith)
      refine ⟨b ^ 2 / (3 * ↑5 ^ (2 * C.smoothness)),
        div_pos (pow_pos hb 2) (mul_pos (by norm_num)
          (Real.rpow_pos_of_pos (by norm_num) _)), ?_⟩
      intro n hn
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      let k := lowSmoothnessGrid d C.smoothness n
      let η := lowSmoothnessAmplitude d C.smoothness b n
      have hg := lowSmoothness_amplitude_legal_guards (d := d) C.smoothness_pos hb.le hnR
        hfield hvariance
      have hbudget : gridUniformScoreBudget P k n η ≤ 1 := by
        have hbt := lowSmoothness_total_score_budget (d := d) C.smoothness_pos hb.le hnR
          (lowSmoothnessScoreConstant_nonneg P)
        have he : gridUniformScoreBudget P k n η =
            lowSmoothnessScoreConstant P *
              (↑n ^ 2 * (lowSmoothnessAmplitude d C.smoothness b n) ^ 4 /
                (lowSmoothnessGrid d C.smoothness n : ℝ) ^ d) := by
          dsimp [gridUniformScoreBudget, lowSmoothnessScoreConstant, k, η]
          ring
        rw [he]
        exact hbt.trans hscore
      have hprior := grid_prior_minimax_lower C P k η b (by have := lowSmoothnessGrid_ge_four (d := d) C.smoothness_pos hnR; dsimp [k]; omega) hs hb.le (hg.1)
        (hg.2.1) (hg.2.2) (by rfl) hholder (lowSmoothness_design_occupancy C.smoothness_pos hd hnR) hbudget
      have hseparation := lowSmoothness_variance_separation (d := d) (b := b)
        C.smoothness_pos hnR
      apply (ENNReal.ofReal_le_ofReal ?_).trans hprior
      calc
        _ = (b ^ 2 / ↑5 ^ (2 * C.smoothness) *
          ↑n ^ (-4 * C.smoothness / (↑d + 4 * C.smoothness))) / 3 := by ring
        _ ≤ η ^ 2 / 3 := div_le_div_of_nonneg_right hseparation (by norm_num)
    · obtain ⟨c, hc, hbound⟩ := (h_low_smoothness_nonparametric_minimax_lower (le_of_not_ge hd))
      refine ⟨c, hc, ?_⟩
      intro n hn
      have h_lowSmoothnessScale_eq_nonparametric : lowSmoothnessScale C.smoothness d n =
          n ^ (-4 * C.smoothness / (d + 4 * C.smoothness)) := by
        have hd  := le_of_not_ge hd
        have hexp : -(1 / 2 ) ≤ -(4 * C.smoothness / (d + 4 * C.smoothness)) := by
          apply neg_le_neg
          apply (div_le_iff₀ (by have : 0 ≤ d := Nat.cast_nonneg d; linarith [C.smoothness_pos])).mpr
          nlinarith
        have hpow := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1 : ℝ) ≤ n) hexp
        have he : -(4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)) =
            -4 * C.smoothness / (d + 4 * C.smoothness) := by ring
        simpa only [lowSmoothnessScale, he] using max_eq_right hpow
      rw [h_lowSmoothnessScale_eq_nonparametric]
      exact hbound n hn
  obtain ⟨c, hc, hbound⟩ := h_low_smoothness_max_minimax_lower
  let A := max (elementaryRMSConstant C) (max 1 c⁻¹)
  have hA : 0 < A := lt_of_lt_of_le (by norm_num) ((le_max_left 1 c⁻¹).trans (le_max_right _ _))
  have hAupper : elementaryRMSConstant C ≤ A := le_max_left _ _
  have hAc : A⁻¹ ≤ c := by
    calc
      A⁻¹ ≤ (c⁻¹)⁻¹ := (inv_le_inv₀ hA (inv_pos.mpr hc)).mpr ((le_max_right 1 c⁻¹).trans (le_max_right _ _))
      _ = c := inv_inv c
  refine ⟨A, hA, ?_⟩
  intro n hn
  have hscale : 0 ≤ lowSmoothnessScale C.smoothness d n := by
    exact (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans (le_max_left _ _)
  constructor
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAc hscale)).trans (hbound n hn)
  have h_elementary_upper_low_smoothness : (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (elementaryRMSConstant C * max ((n : ℝ) ^ (-(1 / 2 : ℝ)))
        ((n : ℝ) ^ (-4 * C.smoothness / ((d : ℝ) + 4 * C.smoothness)))) := by
    have hn : 0 < n := (by omega : 0 < n)
    have h_elementary_rms_upper : (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (elementaryRMSConstant C * max
          ((n : ℝ) ^ (-(1 / 2 : ℝ)))
          ((n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))) := by
      by_cases hn2 : 2 ≤ n
      have h_elementary_rms_upper_of_two_le : (worstCaseRisk C (elementaryEstimator C n)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal (Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) *
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) +
            (n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))) := by
        have hn0 : 0 < n := by omega
        have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn2
        have hnR0 : 0 < (n : ℝ) := by positivity
        have h_elementaryUpperConstant_pos : 0 < elementaryUpperConstant C := by
          have hU : 0 < C.densityUpper := (by norm_num : (0 : ℝ) < 1).trans C.one_lt_densityUpper
          have hR := elementaryRowBound_pos C
          have hK := elementaryKernelBound_pos C
          have hB : 0 ≤ elementaryBiasFactor C := by unfold elementaryBiasFactor; positivity
          unfold elementaryUpperConstant
          positivity
        have hC := h_elementaryUpperConstant_pos.le
        let M := elementaryUpperConstant C *
          pairGridMSEEnvelope d (elementarySmoothness C) n
        have hM0 : 0 ≤ M := by
          dsimp [M, pairGridMSEEnvelope]
          have hnp : 0 < (n : ℝ) - 1 := by linarith
          positivity
        have he : worstCaseRisk C (elementaryEstimator C n) ≤ ENNReal.ofReal M := by
          unfold elementaryEstimator
          rw [dif_pos hn2]
          have h_elementary_grid_worstCaseRisk_le (k : ℕ) (hk : 0 < k) : worstCaseRisk C (elementaryGridEstimator C n k hk) ≤
              ENNReal.ofReal (elementaryUpperConstant C *
              (1 / ↑n + ↑k ^ d / (↑n * (n - 1 : ℕ)) +
                ↑k ^ (-4 * elementarySmoothness C))) := by
            apply iSup_le
            intro θ
            let := sampleLaw_isProbability C θ.val θ.property n
            have hmN : Measurable (elementaryNumerator (d := d) n k hk) :=
              PairUStatistic.pairAverage_measurable n
                (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
                  Prod.snd measurable_snd 0)
            have hmD : Measurable (elementaryDenominator (d := d) n k hk) :=
              PairUStatistic.pairAverage_measurable n
                (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))
            have hT := (stabilizedRatio_error_memLp (sampleLaw θ.val n)
              (a := elementaryFloor d k) hmN hmD θ.property.2.2.2.2.2.1 θ.property.2.2.2.2.2.2.1).integrable_sq
            change Integrable (fun z => ((elementaryGridEstimator C n k hk).val z - θ.val.variance) ^ 2)
              (sampleLaw θ.val n) at hT
            rw [meanSquaredRisk, ← ofReal_integral_eq_lintegral_ofReal hT
              (Eventually.of_forall (fun z => sq_nonneg _))]
            have h_elementary_grid_mse_le : (∫ z, ((elementaryGridEstimator C n k hk).val z - θ.val.variance) ^ 2
                ∂sampleLaw θ.val n) ≤ elementaryUpperConstant C *
                (1 / ↑n + ↑k ^ d / (↑n * (n - 1 : ℕ)) +
                  ↑k ^ (-4 * elementarySmoothness C)) := by
              have h_elementary_grid_mse_explicit : (∫ z, ((elementaryGridEstimator C n k hk).val z - θ.val.variance) ^ 2
                ∂sampleLaw θ.val n) ≤
                (64 * C.densityUpper ^ 2 * elementaryRowBound C +
                  32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2) / ↑n +
                16 * C.densityUpper * (elementaryKernelBound C + C.varianceUpper ^ 2) *
                  ↑k ^ d / (↑n * (n - 1 : ℕ)) +
                2 * C.densityUpper ^ 2 * regularGridOscillation C k ^ 4 := by
                let := observationLaw_isProbability C θ.val θ.property
                let := sampleLaw_isProbability C θ.val θ.property n
                have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ.val)
                  (X := fun _ => id) (fun _ => aemeasurable_id)
                have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ.val) i
                have hmN : Measurable (elementaryNumerator (d := d) n k hk) :=
                  PairUStatistic.pairAverage_measurable n
                    (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
                      Prod.snd measurable_snd 0)
                have hmD : Measurable (elementaryDenominator (d := d) n k hk) :=
                  PairUStatistic.pairAverage_measurable n
                    (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))
                have hS2 : MemLp (fun z => elementaryNumerator n k hk z -
                    θ.val.variance * elementaryDenominator n k hk z) 2 (sampleLaw θ.val n) := by
                  simp_rw [elementary_score_identity θ.val n k hk]
                  exact PairUStatistic.pairAverage_memLp_two
                    (fun i (z : Fin n → Observation d) => z i) hi hp (regularPairScore_memLp C θ.val θ.property k hk)
                have hD2 : MemLp (elementaryDenominator n k hk) 2 (sampleLaw θ.val n) :=
                  PairUStatistic.pairAverage_memLp_two
                    (fun i (z : Fin n → Observation d) => z i) hi hp
                    (sameLabelKernel_memLp (observationLaw θ.val) _ (regularObservationLabel_measurable k hk))
                have hk0 : 0 < ↑k := by exact_mod_cast hk
                have hn0 : 0 < ↑n := by exact_mod_cast (by omega : 0 < n)
                have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
                have ha : 0 < elementaryFloor d k := by unfold elementaryFloor; positivity
                have hED : 2 * elementaryFloor d k ≤ regularGridCollisionMass θ.val k hk := by
                  convert regularGridCollisionMass_lower C θ.val θ.property k hk using 1
                  unfold elementaryFloor
                  field_simp
                have hV0 : 0 ≤ θ.val.variance := C.varianceLower_pos.le.trans θ.property.2.2.2.2.2.1
                have hM := stabilized_ratio_mse_le (sampleLaw θ.val n) hmN hmD hS2 hD2
                  ha θ.property.2.2.2.2.2.1 θ.property.2.2.2.2.2.2.1 hV0 hED
                have h_elementary_score_second_moment_le : (∫ z, (elementaryNumerator n k hk z - θ.val.variance * elementaryDenominator n k hk z) ^ 2
                    ∂sampleLaw θ.val n) ≤
                    8 / ↑n * (C.densityUpper / ↑k ^ d) ^ 2 * elementaryRowBound C +
                    2 / (↑n * (n - 1 : ℕ)) * elementaryKernelBound C *
                      (C.densityUpper / ↑k ^ d) +
                    ((regularGridOscillation C k ^ 2 / 2) * (C.densityUpper / ↑k ^ d)) ^ 2 := by
                  let := observationLaw_isProbability C θ.val θ.property
                  let := sampleLaw_isProbability C θ.val θ.property n
                  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ.val)
                    (X := fun _ => id) (fun _ => aemeasurable_id)
                  have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ.val) i
                  have hS := PairUStatistic.pairAverage_memLp_two
                    (fun i (z : Fin n → Observation d) => z i) hi hp (regularPairScore_memLp C θ.val θ.property k hk)
                  have hmean := PairUStatistic.pairAverage_integral hn2
                    (fun i (z : Fin n → Observation d) => z i) hi hp
                    (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
                      Prod.snd measurable_snd θ.val.variance) (regularPairScore_memLp C θ.val θ.property k hk)
                  let b := ∫ p, regularPairScore θ.val k hk p ∂(observationLaw θ.val).prod (observationLaw θ.val)
                  change (∫ z, PairUStatistic.pairAverage n (regularPairScore θ.val k hk) z
                    ∂sampleLaw θ.val n) = b at hmean
                  have hEq : (∫ z, PairUStatistic.pairAverage n (regularPairScore θ.val k hk) z ^ 2
                      ∂sampleLaw θ.val n) =
                      (∫ z, (PairUStatistic.pairAverage n (regularPairScore θ.val k hk) z - b) ^ 2
                        ∂sampleLaw θ.val n) + b ^ 2 := by
                    have hv := variance_eq_sub hS
                    have hc := variance_eq_integral hS.aemeasurable
                    change variance (fun z => PairUStatistic.pairAverage n (regularPairScore θ.val k hk) z)
                      (sampleLaw θ.val n) = (∫ z, PairUStatistic.pairAverage n (regularPairScore θ.val k hk) z ^ 2
                        ∂sampleLaw θ.val n) - (∫ z, PairUStatistic.pairAverage n (regularPairScore θ.val k hk) z
                          ∂sampleLaw θ.val n) ^ 2 at hv
                    change variance (fun z => PairUStatistic.pairAverage n (regularPairScore θ.val k hk) z)
                      (sampleLaw θ.val n) = ∫ z, (PairUStatistic.pairAverage n (regularPairScore θ.val k hk) z -
                        ∫ z, PairUStatistic.pairAverage n (regularPairScore θ.val k hk) z ∂sampleLaw θ.val n) ^ 2
                        ∂sampleLaw θ.val n at hc
                    rw [hmean] at hv hc
                    dsimp [b]
                    linarith
                  have h_regularPairScore_mean_nonneg : 0 ≤ ∫ z, regularPairScore θ.val k hk z
                ∂(observationLaw θ.val).prod (observationLaw θ.val) := by
                    rw [h_regularPairScore_mean_eq_signal θ.val θ.property k hk]
                    apply integral_nonneg
                    intro z
                    unfold pairWindowScore
                    split_ifs <;> simp only [sub_zero] <;> positivity
                  have hb0 : 0 ≤ b := h_regularPairScore_mean_nonneg
                  have h_regularPairScore_mean_le : (∫ z, regularPairScore θ.val k hk z
                ∂(observationLaw θ.val).prod (observationLaw θ.val)) ≤
                (regularGridOscillation C k ^ 2 / 2) * regularGridCollisionMass θ.val k hk := by
                    let := observationLaw_isProbability C θ.val θ.property
                    have hcube := (observationLaw_fst_measurePreserving C θ.val θ.property).quasiMeasurePreserving.ae
                      (designLaw_cube_ae θ.val)
                    rw [h_regularPairScore_mean_eq_signal θ.val θ.property k hk]
                    have hD := (sameLabelKernel_memLp (observationLaw θ.val) _
                      (regularObservationLabel_measurable k hk)).integrable (by norm_num)
                    have hb : (∫ z, pairWindowScore (regularObservationLabel k hk)
                        (fun z : Observation d => θ.val.regression z.1) 0 z
                        ∂(observationLaw θ.val).prod (observationLaw θ.val)) ≤
                        ∫ z, (regularGridOscillation C k ^ 2 / 2) *
                          sameLabelKernel (regularObservationLabel k hk) z
                          ∂(observationLaw θ.val).prod (observationLaw θ.val) := by
                      have h_regularPairSignal_integrable : Integrable (pairWindowScore (regularObservationLabel k hk)
                        (fun z : Observation d => θ.val.regression z.1) 0)
                        ((observationLaw θ.val).prod (observationLaw θ.val)) := by
                        let := observationLaw_isProbability C θ.val θ.property
                        let R := fun z : Observation d => θ.val.regression z.1
                        have h2 := (observationLaw_regression_memLp_two C θ.val θ.property).integrable_sq
                        have hd : Integrable (fun z : Observation d × Observation d =>
                            R z.1 ^ 2 + R z.2 ^ 2) ((observationLaw θ.val).prod (observationLaw θ.val)) :=
                          (h2.comp_fst _).add (h2.comp_snd _)
                        apply hd.mono'
                          (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
                            R (θ.property.2.1.comp measurable_fst) 0).aestronglyMeasurable
                        filter_upwards [] with z
                        simpa only [abs_zero, add_zero, Real.norm_eq_abs] using
                          pairWindowScore_abs_le (regularObservationLabel k hk) R 0 z
                      apply integral_mono_ae h_regularPairSignal_integrable
                        (hD.const_mul _)
                      filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcube,
                        Measure.quasiMeasurePreserving_snd.ae hcube] with z hz1 hz2
                      by_cases he : regularObservationLabel k hk z.1 = regularObservationLabel k hk z.2
                      have h_regular_grid_same_cell_regression_difference (θ : RegressionParameter d) (hθ : Admissible C θ) (x) (y) (hx : x ∈ unitCube d) (hy : y ∈ unitCube d) (hcell : regularGridCell k hk x = regularGridCell k hk y) : |θ.regression x - θ.regression y| ≤
                          2 * (d + 1) * C.holderBound *
                            (Real.sqrt d * (1 / k)) ^ elementarySmoothness C := by
                        have hr := euclideanNorm_le_coordinate_radius (x - y) (1 / k)
                          (by positivity) (regular_grid_same_cell_radius k hk x y hx hy hcell)
                        have h_admissible_regression_spatial_modulus : |θ.regression x - θ.regression y| ≤
                            2 * (d + 1) * C.holderBound *
                              euclideanNorm (x - y) ^ elementarySmoothness C := by
                          rcases hθ with ⟨_, _, _, _, ⟨F, hcube, hreg, hNorm⟩, _, _, _⟩
                          have hm := RoughRegime.Model.holderBall_spatial_modulus (euclideanExtension F)
                            C.smoothness (2 * C.holderBound)
                            (mul_nonneg (by norm_num) C.holderBound_pos.le)
                            (euclideanExtension_mem_holderBall C F hreg hNorm)
                            (euclideanPoint x) (euclideanPoint y) hx hy
                          have hdiff : euclideanPoint x - euclideanPoint y = euclideanPoint (x - y) :=
                            ((euclideanCoordinates d).symm.map_sub x y).symm
                          rw [hdiff, euclideanPoint_norm] at hm
                          simp only [euclideanExtension, Function.comp_apply, euclideanCoordinates_point,
                            hcube x hx, hcube y hy] at hm
                          unfold elementarySmoothness
                          convert hm using 1 <;> ring
                        apply h_admissible_regression_spatial_modulus.trans
                        apply mul_le_mul_of_nonneg_left
                          (Real.rpow_le_rpow (by unfold euclideanNorm; positivity) hr
                            (elementarySmoothness_pos C).le)
                        exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) C.holderBound_pos.le
                      · have hm := (h_regular_grid_same_cell_regression_difference θ.val θ.property z.1.1 z.2.1 hz1 hz2 he)
                        have hs := pow_le_pow_left₀ (abs_nonneg _) hm 2
                        simp only [sq_abs] at hs
                        simp only [pairWindowScore, sameLabelKernel, ite_eq_left he, sub_zero, mul_one]
                        exact div_le_div_of_nonneg_right hs (by norm_num)
                      · simp [pairWindowScore, sameLabelKernel, he]
                    rw [integral_const_mul, sameLabelKernel_integral (observationLaw θ.val) _
                      (regularObservationLabel_measurable k hk)] at hb
                    simpa only [regularObservationLabel_mass C θ.val θ.property k hk, regularGridCollisionMass] using hb
                  have hbm : b ≤ (regularGridOscillation C k ^ 2 / 2) *
                      (C.densityUpper / ↑k ^ d) :=
                    h_regularPairScore_mean_le.trans
                      (mul_le_mul_of_nonneg_left (regularGridCollisionMass_upper C θ.val θ.property k hk)
                        (by positivity))
                  have hbsq := pow_le_pow_left₀ hb0 hbm 2
                  simp_rw [elementary_score_identity θ.val n k hk]
                  rw [hEq]
                  have h_elementary_score_fluctuation_le : (∫ z, (PairUStatistic.pairAverage n (regularPairScore θ.val k hk) z -
                      ∫ p, regularPairScore θ.val k hk p ∂(observationLaw θ.val).prod (observationLaw θ.val)) ^ 2
                      ∂sampleLaw θ.val n) ≤
                      8 / ↑n * (C.densityUpper / ↑k ^ d) ^ 2 * elementaryRowBound C +
                      2 / (↑n * (n - 1 : ℕ)) * elementaryKernelBound C *
                        (C.densityUpper / ↑k ^ d) := by
                    let := observationLaw_isProbability C θ.val θ.property
                    let := sampleLaw_isProbability C θ.val θ.property n
                    have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ.val)
                      (X := fun _ => id) (fun _ => aemeasurable_id)
                    have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ.val) i
                    have he := PairUStatistic.pairAverage_centered_sq_le hn2
                      (fun i (z : Fin n → Observation d) => z i) hi hp
                      (pairWindowScore_measurable _ (regularObservationLabel_measurable k hk)
                        Prod.snd measurable_snd θ.val.variance) (regularPairScore_memLp C θ.val θ.property k hk)
                      (pairWindowScore_symmetric _ Prod.snd θ.val.variance)
                    have hV0 : 0 ≤ θ.val.variance := C.varianceLower_pos.le.trans θ.property.2.2.2.2.2.1
                    have hVU : θ.val.variance ≤ C.varianceUpper := θ.property.2.2.2.2.2.2.1
                    have : 0 ≤ C.varianceUpper := hV0.trans hVU
                    have : 0 ≤ responseFourthBound C := (responseFourthBound_pos C).le
                    have : 0 ≤ responseSecondBound C := (responseSecondBound_pos C).le
                    have hr : (∫ x, (∫ y, regularPairScore θ.val k hk (x, y) ∂observationLaw θ.val) ^ 2
                        ∂observationLaw θ.val) ≤
                        2 * (C.densityUpper / ↑k ^ d) ^ 2 * elementaryRowBound C := by
                      have h_regularPairScore_row_energy_le : (∫ x, (∫ y, regularPairScore θ.val k hk (x, y) ∂observationLaw θ.val) ^ 2
                ∂observationLaw θ.val) ≤
                2 * (C.densityUpper / ↑k ^ d) ^ 2 *
                  (responseFourthBound C + (|θ.val.variance| + responseSecondBound C) ^ 2) := by
                        let := observationLaw_isProbability C θ.val θ.property
                        let := designLaw_isProbability C θ.val θ.property
                        have hρ  := (by norm_num : (0 : ℝ) < 1).trans C.one_lt_densityUpper
                        have hg : (∫ z : Observation d, z.2 ^ 4 ∂observationLaw θ.val) ≤ responseFourthBound C := by
                          simpa using observationLaw_localized_fourth_integral_le C θ.val θ.property Set.univ MeasurableSet.univ
                        apply pairWindowScore_row_energy_le (observationLaw θ.val) _
                          (regularObservationLabel_measurable k hk) Prod.snd measurable_snd
                          θ.val.variance (responseSecondBound C) (responseFourthBound C)
                          (C.densityUpper / ↑k ^ d) (responseSecondBound_pos C).le
                          (by positivity) (observationLaw_response_memLp_two C θ.val θ.property).integrable_sq
                          (observationLaw_response_fourth_integrable C θ.val θ.property) hg
                        · intro c
                          rw [regularObservationLabel_mass C θ.val θ.property k hk c,
                            regularObservationLabel_fiber k hk c]
                          have hm := observationLaw_localized_second_integral_le C θ.val θ.property
                            ((regularGridCell k hk) ⁻¹' {c})
                            ((measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk))
                          exact hm
                        · intro c
                          rw [regularObservationLabel_mass C θ.val θ.property k hk c]
                          exact regularGridProbability_cap C θ.val θ.property k hk c
                      apply h_regularPairScore_row_energy_le.trans
                      unfold elementaryRowBound
                      rw [abs_of_nonneg hV0]
                      gcongr
                    have := regularGridCollisionMass_upper C θ.val θ.property k hk
                    have : 0 ≤ regularGridCollisionMass θ.val k hk := by
                      unfold regularGridCollisionMass
                      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
                    have hker : (∫ z, regularPairScore θ.val k hk z ^ 2
                        ∂(observationLaw θ.val).prod (observationLaw θ.val)) ≤
                        elementaryKernelBound C * (C.densityUpper / ↑k ^ d) := by
                      have h_regularPairScore_kernel_energy_le : (∫ z, regularPairScore θ.val k hk z ^ 2
                ∂(observationLaw θ.val).prod (observationLaw θ.val)) ≤
                (8 * responseFourthBound C + 2 * θ.val.variance ^ 2) *
                  regularGridCollisionMass θ.val k hk := by
                        let := observationLaw_isProbability C θ.val θ.property
                        have hh := pairWindowScore_energy_le (observationLaw θ.val) _
                          (regularObservationLabel_measurable k hk) Prod.snd measurable_snd
                          θ.val.variance (responseFourthBound C)
                          (observationLaw_response_fourth_integrable C θ.val θ.property) (fun c => by
                            rw [regularObservationLabel_mass C θ.val θ.property k hk c,
                              regularObservationLabel_fiber k hk c]
                            have hm := observationLaw_localized_fourth_integral_le C θ.val θ.property
                              ((regularGridCell k hk) ⁻¹' {c})
                              ((measurableSet_singleton _).preimage (regular_grid_cell_measurable k hk))
                            exact hm)
                        simpa only [regularObservationLabel_mass C θ.val θ.property k hk,
                          regularPairScore, regularGridCollisionMass] using hh
                      apply h_regularPairScore_kernel_energy_le.trans
                      unfold elementaryKernelBound
                      have : θ.val.variance ^ 2 ≤ C.varianceUpper ^ 2 :=
                        pow_le_pow_left₀ hV0 hVU 2
                      gcongr
                    have hn0 : 0 < ↑n := by exact_mod_cast (by omega : 0 < n)
                    have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
                    have hb := he.trans (add_le_add
                      (mul_le_mul_of_nonneg_left hr (by positivity))
                      (mul_le_mul_of_nonneg_left hker (by positivity)))
                    convert hb using 1 <;> first | rfl | ring
                  exact add_le_add h_elementary_score_fluctuation_le hbsq
                have hS := h_elementary_score_second_moment_le
                have h_elementary_denominator_fluctuation_le : (∫ z, (elementaryDenominator n k hk z - regularGridCollisionMass θ.val k hk) ^ 2
                    ∂sampleLaw θ.val n) ≤
                    4 / ↑n * (C.densityUpper / ↑k ^ d) ^ 2 +
                    2 / (↑n * (n - 1 : ℕ)) * (C.densityUpper / ↑k ^ d) := by
                  let := observationLaw_isProbability C θ.val θ.property
                  let := sampleLaw_isProbability C θ.val θ.property n
                  have hi := iIndepFun_pi (μ := fun _ : Fin n => observationLaw θ.val)
                    (X := fun _ => id) (fun _ => aemeasurable_id)
                  have hp := fun i => measurePreserving_eval (fun _ : Fin n => observationLaw θ.val) i
                  have he := PairUStatistic.pairAverage_centered_sq_le hn2
                    (fun i (z : Fin n → Observation d) => z i) hi hp
                    (sameLabelKernel_measurable _ (regularObservationLabel_measurable k hk))
                    (sameLabelKernel_memLp (observationLaw θ.val) _ (regularObservationLabel_measurable k hk))
                    (fun x y => by exact (sameLabelKernel_symmetric _
                      (regularObservationLabel_measurable k hk) (x, y)).symm)
                  change (∫ z, (elementaryDenominator n k hk z -
                      ∫ p, sameLabelKernel (regularObservationLabel k hk) p
                        ∂(observationLaw θ.val).prod (observationLaw θ.val)) ^ 2 ∂sampleLaw θ.val n) ≤ _ at he
                  rw [sameLabelKernel_integral (observationLaw θ.val) _
                    (regularObservationLabel_measurable k hk)] at he
                  simp only [PairUStatistic.rowIntegral] at he
                  rw [sameLabelKernel_row_square_integral (observationLaw θ.val) _
                      (regularObservationLabel_measurable k hk),
                    sameLabelKernel_square_integral (observationLaw θ.val) _
                      (regularObservationLabel_measurable k hk)] at he
                  simp only [regularObservationLabel_mass C θ.val θ.property k hk] at he
                  have hn0 : 0 < ↑n := by exact_mod_cast (by omega : 0 < n)
                  have hn1 : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
                  have h_regularGridCollisionRowEnergy_upper : (∑ c, regularGridProbability θ.val k hk c ^ 3) ≤
                (C.densityUpper / ↑k ^ d) ^ 2 := by
                    apply finite_probability_third_moment_le _ _ (regularGridProbability_nonneg θ.val k hk)
                      (regularGridProbability_sum C θ.val θ.property k hk) (regularGridProbability_cap C θ.val θ.property k hk)
                    exact div_nonneg (by linarith [C.one_lt_densityUpper]) (pow_nonneg (Nat.cast_nonneg k) d)
                  have hr := h_regularGridCollisionRowEnergy_upper
                  have hm := regularGridCollisionMass_upper C θ.val θ.property k hk
                  exact he.trans (add_le_add
                    (mul_le_mul_of_nonneg_left hr (by positivity))
                    (mul_le_mul_of_nonneg_left hm (by positivity)))
                have hD := h_elementary_denominator_fluctuation_le
                have hb := hM.trans (mul_le_mul_of_nonneg_left
                  (add_le_add hS (mul_le_mul_of_nonneg_left hD (sq_nonneg _)))
                  (by positivity : 0 ≤ 2 / elementaryFloor d k ^ 2))
                change (∫ z, ((elementaryGridEstimator C n k hk).val z - θ.val.variance) ^ 2
                  ∂sampleLaw θ.val n) ≤ _ at hb
                convert hb using 1
                unfold elementaryFloor
                field_simp [hk0.ne', hn0.ne', hn1.ne', pow_ne_zero d hk0.ne']
                <;> ring
              have hb := h_elementary_grid_mse_explicit
              have h_regularGridOscillation_fourth : regularGridOscillation C k ^ 4 = elementaryBiasFactor C *
                  ↑k ^ (-4 * elementarySmoothness C) := by
                have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
                have he : ((Real.sqrt d * (1 / (k : ℝ))) ^ elementarySmoothness C) ^ 4 =
                    (Real.sqrt d) ^ (4 * elementarySmoothness C) *
                      (k : ℝ) ^ (-4 * elementarySmoothness C) := by
                  rw [Real.mul_rpow (Real.sqrt_nonneg _) (by positivity), mul_pow,
                    ← Real.rpow_mul_natCast (Real.sqrt_nonneg _),
                    ← Real.rpow_mul_natCast (by positivity : 0 ≤ 1 / (k : ℝ)),
                    one_div, Real.inv_rpow hk0.le, ← Real.rpow_neg hk0.le]
                  congr 2 <;> ring
                unfold regularGridOscillation elementaryBiasFactor
                rw [mul_pow, he]
                ring
              rw [h_regularGridOscillation_fourth] at hb
              have : 0 < ↑n := by exact_mod_cast (by omega : 0 < n)
              have : 0 < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n - 1)
              have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
              have hU : 0 < C.densityUpper := (by norm_num : (0 : ℝ) < 1).trans C.one_lt_densityUpper
              have hR := (elementaryRowBound_pos C).le
              have := (elementaryKernelBound_pos C).le
              have : 0 ≤ elementaryBiasFactor C := by unfold elementaryBiasFactor; positivity
              apply hb.trans
              let A := 64 * C.densityUpper ^ 2 * elementaryRowBound C +
                32 * C.densityUpper ^ 2 * C.varianceUpper ^ 2
              let B := 16 * C.densityUpper * (elementaryKernelBound C + C.varianceUpper ^ 2)
              let E := 2 * C.densityUpper ^ 2 * elementaryBiasFactor C
              have : 0 ≤ A := by dsimp [A]; positivity
              have : 0 ≤ B := by dsimp [B]; positivity
              have : 0 ≤ E := by dsimp [E]; positivity
              have h1 := mul_le_mul_of_nonneg_right (show A ≤ A + B + E by linarith)
                (show 0 ≤ 1 / ↑n by positivity)
              have h2 := mul_le_mul_of_nonneg_right (show B ≤ A + B + E by linarith)
                (show 0 ≤ (k : ℝ) ^ d / ((n : ℝ) * (n - 1 : ℕ)) by positivity)
              have h3 := mul_le_mul_of_nonneg_right (show E ≤ A + B + E by linarith)
                (Real.rpow_pos_of_pos hk0 (-4 * elementarySmoothness C)).le
              dsimp [A, B, E] at h1 h2 h3
              unfold elementaryUpperConstant
              convert add_le_add (add_le_add h1 h2) h3 using 1 <;> ring
            exact ENNReal.ofReal_mono h_elementary_grid_mse_le
          have hh := h_elementary_grid_worstCaseRisk_le (elementaryChosenGrid C n) (elementaryChosenGrid_pos C hn0)
          convert hh using 1
          dsimp [M, pairGridMSEEnvelope, elementaryChosenGrid]
          rw [Nat.cast_sub (by omega : 1 ≤ n)]
          norm_num
        have hh := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rw [ENNReal.ofReal_rpow_of_nonneg hM0 (by norm_num), ← Real.sqrt_eq_rpow] at hh
        have hs : Real.sqrt M ≤ Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) *
            ((n : ℝ) ^ (-(1 / 2 : ℝ)) +
              (n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C))) := by
          apply pairGrid_rms_of_mse_bound (elementarySmoothness_pos C) hnR hC (Real.sqrt_nonneg M)
          exact le_of_eq (Real.sq_sqrt hM0)
        exact hh.trans (ENNReal.ofReal_mono hs)
      · apply h_elementary_rms_upper_of_two_le.trans
        apply ENNReal.ofReal_mono
        have hA : 0 ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
        have hB : 0 ≤ (n : ℝ) ^
            (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)) := by positivity
        have hs : 0 ≤ Real.sqrt (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1)) :=
          Real.sqrt_nonneg _
        have hdiam : 0 ≤ C.varianceUpper - C.varianceLower := sub_nonneg.mpr C.variance_interval.le
        have hmax := le_max_left ((n : ℝ) ^ (-(1 / 2 : ℝ)))
          ((n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))
        have hmax' := le_max_right ((n : ℝ) ^ (-(1 / 2 : ℝ)))
          ((n : ℝ) ^ (-4 * elementarySmoothness C / ((d : ℝ) + 4 * elementarySmoothness C)))
        have hm0 := hA.trans hmax
        unfold elementaryRMSConstant
        nlinarith [mul_nonneg hdiam hm0]
      · have hn1 : n = 1 := by omega
        subst n
        unfold elementaryEstimator
        rw [dif_neg (by decide : ¬2 ≤ (1 : ℕ))]
        have he : worstCaseRisk C (constantEstimator d 1 C.varianceLower) ≤
            ENNReal.ofReal ((C.varianceUpper - C.varianceLower) ^ 2) := by
          apply iSup_le
          intro θ
          exact constantEstimator_risk_bound C θ.val θ.property
        have hh := ENNReal.rpow_le_rpow he (by norm_num : (0 : ℝ) ≤ 1 / 2)
        rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num),
          ← Real.sqrt_eq_rpow, Real.sqrt_sq (sub_nonneg.mpr C.variance_interval.le)] at hh
        apply hh.trans
        apply ENNReal.ofReal_mono
        simp only [Nat.cast_one, Real.one_rpow, max_self, mul_one]
        unfold elementaryRMSConstant
        have hs := Real.sqrt_nonneg (elementaryUpperConstant C * (2 * (5 : ℝ) ^ d + 1))
        linarith
    simpa only [elementarySmoothness, min_eq_left hs] using h_elementary_rms_upper
  · have hupper := (ENNReal.rpow_le_rpow
        (minimaxRisk_le_worstCaseRisk C (elementaryEstimator C n))
        (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans
      h_elementary_upper_low_smoothness
    have he : -4 * C.smoothness / (d + 4 * C.smoothness) =
        -(4 * C.smoothness / (d + 4 * C.smoothness)) := by ring
    change minimaxRMS C n ≤ _ at hupper
    have hu : minimaxRMS C n ≤ ENNReal.ofReal
        (elementaryRMSConstant C * lowSmoothnessScale C.smoothness d n) := by
      simpa only [he, lowSmoothnessScale] using hupper
    exact hu.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hAupper hscale))
end NearlyMinimax
