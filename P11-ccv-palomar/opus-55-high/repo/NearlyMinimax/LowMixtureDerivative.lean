module

public import NearlyMinimax.LowSmoothness
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Differentiation of the actual finite latent experiment after integration
over a finite design measure. Uniform domination is proved from finite polynomial
formulas on a compact box; no bound on the score is assumed. -/

open MeasureTheory Set Filter Metric
𝚶
𝚨

𝗇 𝔮 𝙈
𝗇 𝔈 𝔮 → ℝ
𝗇 𝔯 Fin m → Fin 3
𝗇 𝔉 𝔯 → 𝙔
abbrev FiniteExperimentData (m n : ℕ) :=
  ℝ × 𝔉 × 𝔈

𝗇 𝔄 v - 𝙎 * t
𝗇 𝔖 𝙎
𝗇 𝔙 activationProductPrior m t ξ
𝗃 𝔲 ἀ m n a
𝗇 𝔰 𝔲 finiteResponseLikelihood
𝗇 𝔛 𝔰 𝔄 f ξ y
def finiteExperimentRawDerivative (m n : ℕ) (a v η t : ℝ)
    (f : 𝔉) (T : 𝔈) : ℝ :=
  ∑ ξ, (activationProductPriorDerivative m t ξ *
       ∑ y, 𝔛 * T y +
    𝔙 *
       ∑ y, (∑ i, 𝔲 finiteResponseVarianceTerm 𝔄 f ξ y i) *
         -𝔖 * T y )

𝗃 𝔣 𝔲 ἀ v η
𝗇 𝔟 𝔣 finiteExperimentRawDerivative
𝗇 𝔚 𝔟 t f T
𝗇 𝔡 𝔣 finiteExperimentExpectation
𝗇 𝔞 𝔡
theorem finite_experiment_raw_hasDerivAt m n a v η t
    f T :
    HasDerivAt (fun u => 𝔞 u f T)
      𝔚 t := by
  have hV : HasDerivAt (fun u => v - 𝔖 * u) (-𝔖) t :=
    ((hasDerivAt_const t v).sub $ (hasDerivAt_id t).const_mul 𝔖 ).congr_deriv 𝖢₃
  apply HasDerivAt.fun_sum
  intro ξ _
  apply (activation_product_prior_hasDerivAt m t ξ).mul
  apply HasDerivAt.fun_sum
  intro y _
  exact ((𝔲 finite_response_variance_hasDerivAt 𝔄 f ξ y).comp t hV).mul_const $ T y

theorem ternaryMass_joint_continuous a y :
    Continuous fun z : 𝚑 => ternaryMass a z.1 z.2 y := by
  fin_cases y <;> simp [ternaryMass] <;> fun_prop

𝗇 𝔠 FiniteExperimentData m n
section

variable (m n : ℕ)
    (a v η : ℝ)
    (ξ : 𝔯)
    (y : 𝔮)

𝗇 𝔥 v - 𝔖 * z.1
𝗃 𝔳 fun z : 𝔠 => z.2.1 ξ ἀ
𝗃 𝔶 (ternaryMass_joint_continuous a $ y ἀ ).comp
private theorem finite_response_data_continuous :
    Continuous fun z : 𝔠 =>
      𝔰 𝔥 z.2.1 ξ y := by
  apply continuous_finset_prod
  intro i _
  exact 𝔶 i
    $ (show Continuous 𝔳 i from 𝖦₃).prodMk
      𝖦₃

private theorem finite_variance_data_continuous (i : Fin n) :
    Continuous fun z : 𝔠 =>
      𝔲 finiteResponseVarianceTerm 𝔥 z.2.1 ξ y i := by
  apply Continuous.const_mul
  apply continuous_finset_prod
  intro k _
  exact 𝔶 k
    $ (show Continuous 𝔳 k from 𝖦₃).prodMk
      𝖦₃

end

𝗇 𝔎 (𝔣 finite_response_data_continuous ξ y).mul $ (continuous_apply y).comp $ continuous_snd.comp continuous_snd
𝗃 𝔷 fun z : 𝔠 => ἀ z.1 z.2.1 z.2.2
𝗇 𝔏 𝔷 𝔡
𝗇 𝔔 (continuous_iff_continuousAt.mpr fun t => (activation_product_prior_hasDerivAt m t ξ).continuousAt ).comp continuous_fst
theorem finite_experiment_expectation_data_continuous m n a v η :
    Continuous 𝔏 := by
  apply continuous_finset_sum
  intro ξ _
  apply Continuous.mul
  · exact 𝔔
  · apply continuous_finset_sum
    intro y _
    exact 𝔎

𝗇 𝔐 𝔷 𝔟
theorem finite_experiment_raw_derivative_data_continuous m n a v η :
    Continuous 𝔐 := by
  apply continuous_finset_sum
  intro ξ _
  apply Continuous.add
  · apply Continuous.mul
    · apply continuous_finset_sum
      intro j _
      apply Continuous.const_mul
      apply continuous_finset_prod
      intro k _
      exact (continuous_iff_continuousAt.mpr fun t =>
        (activation_prior_hasDerivAt t $ ξ k ).continuousAt ).comp continuous_fst
    · apply continuous_finset_sum
      intro y _
      exact 𝔎
  · apply Continuous.mul
    · exact 𝔔
    · apply continuous_finset_sum
      intro y _
      apply Continuous.mul
      · apply Continuous.mul_const
        apply continuous_finset_sum
        intro i _
        exact 𝔣 finite_variance_data_continuous ξ y i
      fun_prop

𝗇 𝔓 𝔣 finite_experiment_raw_derivative_data_continuous
/-- Both the expectation and its raw derivative are bounded on each finite
parameter box, including parameter values outside the probability interval. -/
theorem finite_experiment_uniform_box_bound m n a v η R :
    ∃ B , 𝘶₁ ∧ ∀ t
      f T,
      |t| ≤ R → ‖f‖ ≤ R → ‖T‖ ≤ R →
      ‖𝔞 t f T‖ ≤ B ∧
      ‖𝔚‖ ≤ B := by
  let G : 𝔠 → 𝚑 := fun z =>
    (𝔞 z.1 z.2.1 z.2.2,
      𝔟 z.1 z.2.1 z.2.2)
  have hG := (𝔣 finite_experiment_expectation_data_continuous).prodMk
    𝔓
  obtain ⟨C, hC⟩ := (isCompact_closedBall 0 R).exists_bound_of_continuousOn hG.continuousOn
  refine ⟨max 1 C, 𝘏, ?_⟩
  aesop

section Integrated
variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]

𝗃 𝔵 ἀ t (f x) $ T x
𝗇 𝔅 𝔵 𝔟
𝗃 𝔤 ἀ u (f x) $ T x
𝗇 𝔇 𝔤 𝔡
𝗇 𝔊 ∀ᵐ x ∂μ, ‖f x‖ ≤ ρ
𝗇 𝔍 ∀ᵐ x ∂μ, ‖T x‖ ≤ M
𝗇 𝔒 fun u x => 𝔤 𝔟
𝗇 𝔗 ‖u - t‖
𝗇 𝔘 (u, (f x, T x))
𝗇 𝔜 fun u => ∫ x, 𝔇 ∂μ
𝗇 𝔦 𝘌₂ ≤ 𝔗 + ‖t‖
𝗇 𝔧 fun x => 𝔅
𝗇 𝔨 ∫ x, 𝔅 ∂μ
𝗇 𝔩 max ρ M
𝗇 𝔪 le_max_right _ _
𝗇 𝔫 𝚂₁
𝗇 𝔬 ‖D u x‖ ≤ B
𝗇 𝔭 _ ≤ 1 + ‖t‖
𝗃 𝔱 Filter.Eventually.of_forall fun u => (ἀ u).aestronglyMeasurable
𝗃 𝔴 (ἀ ρ M).trans 𝔪
set_option maxHeartbeats 200000 in
/-- Bounded measurable fields and data observables can be differentiated after
integration over the actual design law. The domination needed for interchange
is derived from the finite polynomial formulas. -/
theorem finite_experiment_integrated_raw_hasDerivAt (m n : ℕ) (a v η t ρ M : ℝ)
    (f : α → 𝔉) (T : α → 𝔈)
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : 𝔊) (hTBound : 𝔍) :
    Integrable 𝔧 μ ∧
      HasDerivAt 𝔜
        𝔨 t := by
  let R := max (|t| + 1) 𝔩
  obtain ⟨B, hB, hBox⟩ := 𝔣 finite_experiment_uniform_box_bound R
  let F : ℝ → 𝘬 := fun u x => 𝔇
  let D : ℝ → 𝘬 := 𝔒
  have hData (u : ℝ) : Measurable fun x : α => 𝔘 :=
    measurable_const.prodMk $ hf.prodMk hT
  have hFData : Measurable 𝔏 :=
    (𝔣 finite_experiment_expectation_data_continuous).measurable
  have hDData : Measurable 𝔐 :=
    (𝔓).measurable
  have hFmeas (u : ℝ) : Measurable $ F u := by
    have hComp := hFData.comp $ hData u
    exact hComp
  have hDmeas (u : ℝ) : Measurable $ D u := by
    have hComp := hDData.comp $ hData u
    exact hComp
  have hFields : ∀ᵐ x ∂μ, ‖f x‖ ≤ R ∧ ‖T x‖ ≤ R := by
    filter_upwards [hfBound, hTBound] with x hfx hTx
    exact ⟨hfx.trans 𝔴 le_max_left,
      hTx.trans 𝔴 le_max_right⟩
  have htR : |t| ≤ R := (le_add_of_nonneg_right (by norm_num : 𝙋 ≤ 1)).trans 𝔫
  have hFint : Integrable (F t) μ := Integrable.of_bound (hFmeas t).aestronglyMeasurable B $ by
    filter_upwards [hFields] with x hx
    exact (𝔵 hBox htR hx.1 hx.2).1
  have hDom : ∀ᵐ x ∂μ, ∀ u ∈ ball t 1, 𝔬 := by
    filter_upwards [hFields] with x hx
    intro u hu
    have hut : 𝔗 < 1 := by simpa only [mem_ball, dist_eq_norm] using hu
    have huR : |u| ≤ R := by
      have huNorm : 𝘌₂ ≤ |t| + 1 := calc
        𝔦 := norm_le_norm_sub_add u t
        𝔭 := add_le_add hut.le le_rfl
        _ = |t| + 1 := by rw [Real.norm_eq_abs]; ring
      have huAbs : |u| ≤ |t| + 1 := by simpa only [Real.norm_eq_abs] using huNorm
      exact huAbs.trans 𝔫
    exact (𝔤 hBox huR hx.1 hx.2).2
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (F := F) (F' := D) (bound := fun _ => B) (s := ball t 1)
    (ball_mem_nhds t 𝖠₄ )
    𝔱 hFmeas hFint
    (hDmeas t).aestronglyMeasurable hDom (integrable_const B)
    $ Filter.Eventually.of_forall fun x u _ => 𝔣 finite_experiment_raw_hasDerivAt u (f x) $ T x

theorem finite_experiment_raw_derivative_eq_score m n a v η t
    f T
    (hpositive : ∀ ξ y, 0 < 𝔛) :
    𝔚 =
      ∑ ξ, 𝔙 * ∑ y,
        𝔛 *
          T y * 𝔲 finiteExperimentScore 𝔄 η f ξ y :=
  (𝔣 finite_experiment_raw_hasDerivAt t f T).unique
    $ 𝔣 finite_experiment_observable_score_hasDerivAt t f T hpositive

/-- The integrated derivative is continuous, so its interval integrability
on a bounded parameter path is a consequence of the actual finite formulas. -/
theorem finite_experiment_integrated_raw_derivative_continuous m n a v η ρ M
    f T
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : 𝔊) (hTBound : 𝔍) :
    Continuous fun t => 𝔨 := by
  apply continuous_iff_continuousAt.mpr
  intro t
  let R := max (|t| + 1) 𝔩
  obtain ⟨B, hB, hBox⟩ := 𝔣 finite_experiment_uniform_box_bound R
  let D := 𝔒
  have hDData :=
    (𝔓).measurable
  have hDmeas u : Measurable $ D u := by
    fun_prop
  have hDom : ∀ᶠ u in 𝓝 t, ∀ᵐ x ∂μ, 𝔬 := by
    filter_upwards [ball_mem_nhds t (by norm_num : 𝙋 < 1)] with u hu
    filter_upwards [hfBound, hTBound] with x hfx hTx
    have hut : 𝔗 < 1 := by assumption
    have huR : |u| ≤ R := by
      have huNorm := calc
        𝔦 := norm_le_norm_sub_add u t
        𝔭 := add_le_add hut.le le_rfl
        _ = |t| + 1 := by rw [Real.norm_eq_abs]; ring
      bound
    grind
  have hCont : ∀ᵐ x ∂μ, ContinuousAt (fun u => D u x) t := by
    apply Filter.Eventually.of_forall
    intro x
    have hDataCont : Continuous fun u : ℝ => 𝔘 :=
      continuous_id.prodMk continuous_const
    have hComp := (𝔓).comp hDataCont
    exact hComp.continuousAt
  exact continuousAt_of_dominated
    𝔱 hDmeas hDom (integrable_const B) hCont

𝗇 𝔢 𝔰 𝔄 (f x) ξ y
𝗇 𝔑 fun x => ∑ ξ, 𝔙 * ∑ y, 𝔢 * T x y * 𝔲 finiteExperimentScore 𝔄 η (f x) ξ y
/-- Exact score representation after integrating over the design. Likelihood
positivity is needed only at the differentiation point. -/
theorem finite_experiment_integrated_score_hasDerivAt m n a v η t ρ M
    f (T : α → 𝔈)
    (hf : Measurable f) (hT : Measurable T)
    (hfBound : 𝔊) (hTBound : 𝔍)
    (hpositive : ∀ᵐ x ∂μ, ∀ ξ y,
      0 < 𝔢) :
    let S := 𝔑
    Integrable S μ ∧ HasDerivAt
      𝔜
      (∫ x, S x ∂μ) t := by
  obtain ⟨hInt, hDeriv⟩ := finite_experiment_integrated_raw_hasDerivAt μ m n a v η t ρ M f T hf hT hfBound hTBound
  have he : 𝔧 =ᵐ[μ]
      𝔑 := by
    filter_upwards [hpositive] with x hx
    exact 𝔣 finite_experiment_raw_derivative_eq_score t (f x) (T x) hx
  exact ⟨hInt.congr he, integral_congr_ae he ▸ hDeriv⟩
