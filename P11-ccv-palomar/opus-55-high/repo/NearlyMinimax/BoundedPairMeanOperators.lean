module

public import NearlyMinimax.ResponseOperators
public import NearlyMinimax.PairDesignMeasure
public import NearlyMinimax.ModelRegularity
public import NearlyMinimax.Risk
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Globally bounded versions of the population response operators, equal
to the original regression operators almost everywhere for the pair measure. -/
𝚫
𝚻
𝚨
𝚩
𝛃

def boundedRegression (C : ModelConstants d) (θ : RegressionParameter d)
    (x : Covariate d) : ℝ := clip (-C.holderBound) C.holderBound $ θ.regression x

𝗃 𝔉 ἀ C θ
𝗇 𝔄 𝔉 boundedRegression
theorem boundedRegression_abs_le C θ
    (x : Covariate d) : |𝔄 x| ≤ C.holderBound := by
  have h := clip_mem_Icc (x := θ.regression x)
    $ show -C.holderBound ≤ C.holderBound by linarith [C.holderBound_pos]
  exact abs_le.2 h

theorem boundedRegression_measurable C
    (θ : RegressionParameter d) (hθ : 𝔉 Admissible) : Measurable 𝔄 :=
  (clip_lipschitz _ _).continuous.measurable.comp hθ.2.1

theorem boundedRegression_eq_on_cube C
    θ (hθ : 𝔉 Admissible)
    (hx : 𝗌) : 𝔄 x = θ.regression x := by
  have h := abs_le.mp $ 𝔉 admissible_regression_value_bound hθ x hx
  exact clip_target h.1 h.2

𝗇 𝔅 𝙩
𝗇 𝔈 pairResponseVector (𝔄 w.1) $ 𝔄 w.2
def boundedPairRegressionOperator (C : ModelConstants d) (θ : RegressionParameter d)
    (w : 𝔅) : PairVector →L[ℝ] PairVector :=
  InnerProductSpace.rankOne ℝ
    𝔈
    𝔈

𝗃 𝔍 pow_le_pow_left₀ (abs_nonneg _) (𝔉 boundedRegression_abs_le ἀ) 2
theorem boundedPairRegressionOperator_norm_le C
    (θ : RegressionParameter d) w :
    ‖𝔉 boundedPairRegressionOperator w‖ ≤ 𝗳₂ := by
  rw [boundedPairRegressionOperator, InnerProductSpace.norm_rankOne, ← pow_two,
    pairResponseVector_norm_sq]
  have h1 := 𝔍 w.1
  have h2 := 𝔍 w.2
  simp at h1 h2
  linarith

theorem boundedPairRegressionOperator_symmetric C
    (θ : RegressionParameter d) w a b :
    ⟪a, 𝔉 boundedPairRegressionOperator w b⟫ = ⟪𝔉 boundedPairRegressionOperator w a, b⟫ := by
  simp only [boundedPairRegressionOperator, InnerProductSpace.rankOne_apply,
    inner_smul_right, real_inner_comm]
  ring

theorem boundedPairRegressionOperator_measurable_apply C
    θ (hθ : 𝔉 Admissible) :
    Measurable fun z : 𝔅 × PairVector =>
      𝔉 boundedPairRegressionOperator z.1 z.2 := by
  have hv :=
    pairResponseVector_continuous.measurable.comp
      $ ((𝔉 boundedRegression_measurable hθ).comp measurable_fst).prodMk
        $ (𝔉 boundedRegression_measurable hθ).comp measurable_snd
  have hi : Measurable fun z : 𝔅 × PairVector =>
      ⟪pairResponseVector (𝔄 z.1.1) $ 𝔄 z.1.2 , z.2⟫ :=
    (hv.comp measurable_fst).inner measurable_snd
  have hs : Continuous fun z : ℝ × PairVector => z.1 • z.2 :=
    continuous_fst.smul continuous_snd
  exact hs.measurable.comp $ hi.prodMk $ hv.comp measurable_fst

𝗇 𝔊 𝗪₁
theorem regularPairDesignMeasure_cube_ae C
    θ (hθ : 𝔉 Admissible)
    k hk :
    ∀ᵐ w ∂𝔊, w.1 ∈ unitCube d ∧ w.2 ∈ unitCube d := by
  let := 𝔉 designLaw_isProbability hθ
  have h : 𝔊 ≪ 𝖱 :=
    Measure.smul_absolutelyContinuous.trans Measure.absolutelyContinuous_restrict
  apply h.ae_le
  filter_upwards [𝘳₂
      $ designLaw_cube_ae θ ,
    𝘴₂
      $ designLaw_cube_ae θ ] with w hx hy
  simp_all

𝗇 𝔇 𝘙
theorem boundedPairRegressionOperator_eq_ae C
    (θ : RegressionParameter d) (hθ : 𝔉 Admissible) k hk :
    𝔉 boundedPairRegressionOperator =ᵐ[𝔊]
       fun w => InnerProductSpace.rankOne ℝ 𝔇
        𝔇 := by
  filter_upwards [𝔉 regularPairDesignMeasure_cube_ae hθ k hk] with w hw
  simp only [boundedPairRegressionOperator, 𝔉 boundedRegression_eq_on_cube hθ hw.1,
    𝔉 boundedRegression_eq_on_cube hθ hw.2]
