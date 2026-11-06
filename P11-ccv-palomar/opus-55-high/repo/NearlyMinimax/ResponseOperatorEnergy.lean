module

public import NearlyMinimax.ResponseOperators
public import NearlyMinimax.PairWindowModel
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Localized fourth-moment control of the actual response operators. -/
𝚫
𝚪
𝚨
𝚬
𝚩

section Partition
variable {E I : Type*} [MeasurableSpace E] [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I] [MeasurableEq I]
variable (μ : Measure E) [IsProbabilityMeasure μ]
  (label : E → I) (hlabel : Measurable label)
  (r : 𝙏) (hmr : Measurable r)
include hlabel hmr

𝗃 𝔗 ἀ V (r z.1) $ r z.2
def localizedResponseOperatorEnergy (V : ℝ) (z : 𝖸₂) : ℝ :=
  sameLabelKernel label z * ‖𝔗 pairScoreOperator‖ ^ 2

𝗇 𝔄 fun x => r x ^ 4
𝗇 𝔎 6 + 8 * V ^ 2
𝗇 𝔅 6 * G z + 6 * G z.swap + 𝔎 * sameLabelKernel label z
𝗇 𝔇 (hG.const_mul 6).add $ hGs.const_mul 6
𝗇 𝔍 𝔗 pairScoreOperator_norm_sq_le
𝗇 𝔏 localizedResponseOperatorEnergy label r V
𝗇 𝔐 (𝔇).add $ hq.const_mul _
𝗃 𝔖 ἀ μ label hlabel
𝗇 𝔓 (𝔖 sameLabelKernel_memLp).integrable
theorem localizedResponseOperatorEnergy_integrable V
    (hr4 : Integrable 𝔄 μ) :
    Integrable 𝔏 $ μ.prod μ := by
  let G := labelLocalizedKernel label 𝔄
  have hG := 𝔖 labelLocalizedKernel_integrable _ hr4
  have hGs :=
    integrable_swap_iff.mpr hG
  have hq := 𝔓 𝖠₄
  have hi : Integrable (fun z =>
      𝔅) $ μ.prod μ :=
    𝔐
  have hm : Measurable 𝔏 := by
    apply (sameLabelKernel_measurable label hlabel).mul
    exact ((pairScoreOperator_continuous V).measurable.comp
      $ (hmr.comp measurable_fst).prodMk $ hmr.comp measurable_snd ).norm.pow_const 2
  apply hi.mono' hm.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg
    $ mul_nonneg (by unfold sameLabelKernel; positivity) $ sq_nonneg _ ]
  by_cases he : 𝚌₁
  · have hb := 𝔍
    simpa only [localizedResponseOperatorEnergy, sameLabelKernel, he, if_pos,
      labelLocalizedKernel, G, Prod.fst_swap, Prod.snd_swap, eq_comm, one_mul, mul_one] using
        𝖡₄
  · simp [localizedResponseOperatorEnergy, sameLabelKernel, labelLocalizedKernel, G,
      he, Ne.symm he]

𝗇 𝔈 label ⁻¹' {i}
𝗇 𝔉 ∫ z, 𝔏 z ∂μ.prod μ
theorem localizedResponseOperatorEnergy_integral_le V B4
    (hr4 : Integrable 𝔄 μ)
    (hloc : ∀ i , ∫ x, (𝔈).indicator 𝔄 x ∂μ ≤
      B4 * μ.real 𝔈) :
    𝔉 ≤
      (12 * B4 + 6 + 8 * V ^ 2) * ∑ i : I, μ.real 𝔈 ^ 2 := by
  let G := labelLocalizedKernel label 𝔄
  have hG := 𝔖 labelLocalizedKernel_integrable _ hr4
  have hGs :=
    integrable_swap_iff.mpr hG
  have hq := 𝔓 𝖠₄
  have hupper := 𝔖 labelLocalizedKernel_integral_le _ hr4 B4 hloc
  have hb : 𝔉 ≤
      ∫ z : 𝖸₂, 𝔅 ∂μ.prod μ := by
    apply integral_mono (𝔖 localizedResponseOperatorEnergy_integrable r hmr V hr4)
      𝔐
    intro z
    simp
    by_cases he : 𝚌₁
    · have hb := 𝔍
      simp only [localizedResponseOperatorEnergy, sameLabelKernel, he, if_pos,
        labelLocalizedKernel, Prod.fst_swap, Prod.snd_swap]
      nlinarith
    · simp [localizedResponseOperatorEnergy, sameLabelKernel, labelLocalizedKernel, he, Ne.symm he]
  have ha := integral_add 𝔇 $ hq.const_mul 𝔎
  have ha' := integral_add (hG.const_mul 6) $ hGs.const_mul 6
  simp at ha ha'
  rw [ha, ha', integral_const_mul, integral_const_mul, integral_const_mul,
    integral_prod_swap G, 𝔖 sameLabelKernel_integral] at hb
  nlinarith

end Partition

def responseOperatorEnergyBound (C : ModelConstants d) : ℝ :=
  12 * responseFourthBound C + 6 + 8 * C.varianceUpper ^ 2

theorem responseOperatorEnergyBound_pos (C : ModelConstants d) :
    0 < responseOperatorEnergyBound C := by
  have h4 := responseFourthBound_pos C
  unfold responseOperatorEnergyBound
  positivity

𝗇 𝔊 𝖶
𝗇 𝔑 localizedResponseOperatorEnergy (regularObservationLabel k hk) Prod.snd θ.variance
𝗃 𝔒 ἀ C θ hθ
𝗇 𝔔 regularObservationLabel_measurable k hk
𝗃 𝔘 ἀ (observationLaw θ) _ 𝔔 Prod.snd measurable_snd θ.variance
theorem regularResponseOperatorEnergy_integrable C
    (θ : RegressionParameter d) (hθ : 𝙟) k hk :
    Integrable 𝔑 𝔊 := by
  let := 𝔒 observationLaw_isProbability
  exact 𝔘 localizedResponseOperatorEnergy_integrable
      𝔒 observationLaw_response_fourth_integrable

theorem regularResponseOperatorEnergy_le C
    (θ : RegressionParameter d) (hθ : 𝙟) k hk :
     ∫ z, 𝔑 z ∂𝔊 ≤
      responseOperatorEnergyBound C * (C.densityUpper / 𝗋) := by
  let := 𝔒 observationLaw_isProbability
  have hb := 𝔘 localizedResponseOperatorEnergy_integral_le
    (responseFourthBound C) 𝔒 observationLaw_response_fourth_integrable $ by
      intro i
      rw [𝔒 regularObservationLabel_mass k hk i, regularObservationLabel_fiber k hk i]
      exact 𝔒 observationLaw_localized_fourth_integral_le _
        $ (measurableSet_singleton i).preimage $ regular_grid_cell_measurable k hk
  simp_rw [𝔒 regularObservationLabel_mass k hk] at hb
  have hV0 := C.varianceLower_pos.le.trans hθ.2.2.2.2.2.1
  have hVup := hθ.2.2.2.2.2.2.1
  have hmass : 0 ≤ 𝘬₁ := by
    unfold regularGridCollisionMass
    positivity
  apply hb.trans
  calc
    _ ≤ responseOperatorEnergyBound C * 𝘬₁ := by
      apply mul_le_mul_of_nonneg_right _ hmass
      unfold responseOperatorEnergyBound
      nlinarith
    𝖦 := mul_le_mul_of_nonneg_left (𝔒 regularGridCollisionMass_upper k hk)
      (responseOperatorEnergyBound_pos C).le
