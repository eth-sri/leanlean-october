module

public import NearlyMinimax.PairOperatorMean
public import NearlyMinimax.PilotMeanLaw
public import NearlyMinimax.TwoStagePairRisk
public import NearlyMinimax.BoundedPairMeanOperators
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Actual same-cell pair conditional means and their two-pilot mean risk. -/
𝚫
open scoped RealInnerProductSpace ENNReal
𝚨

𝛂

𝗇 𝔅 𝙩
𝗇 𝕺 𝔅 → PairVector
𝗇 𝖇 Ω → 𝕺
def pairPilotCoefficient (bar : 𝕺)
    (η : 𝖇) (x : Ω)
    (w : 𝔅) : PairVector := bar w + η x w

𝗇 𝖒 𝘯
𝗇 𝔚 sameLabelKernel 𝖒
𝗇 𝖓 pairPilotCoefficient bar η
𝗇 𝔞 𝖓 x.1
𝗇 𝔟 𝖓 x.2
𝗇 𝔤 𝖰
𝗇 𝔮 𝚎
𝗇 𝖌 𝗰 → ℝ
def pairPilotScoreKernel (θ : RegressionParameter d) (k : ℕ) (hk : 𝔤)
    (bar : 𝕺)
    (η : 𝖇) (x : 𝔮) :
    𝖌 :=
  pairScoreFieldKernel θ 𝔞 𝔟
    𝔚

def pairPilotNoiseKernel (k : ℕ) (hk : 𝔤)
    (bar : 𝕺)
    (η : 𝖇) (x : 𝔮) :
    𝖌 :=
  pairNoiseFieldKernel 𝔞 𝔟
    𝔚

𝗇 𝔯 𝙦 ^ d
𝗇 𝖊 PairUStatistic.fieldPairMean (μ := observationLaw θ) 𝔯
𝗃 𝖞 ἀ θ k hk bar η
𝗇 𝖑 𝖞 pairPilotScoreKernel
def pairPilotScoreMean (θ : RegressionParameter d) (k : ℕ) (hk : 𝔤)
    (bar : 𝕺)
    (η : 𝖇) (x : 𝔮) : ℝ :=
  𝖊
    𝖑 x

𝗇 𝖔 𝖪₂
def pairPilotNoiseMean (θ : RegressionParameter d) (k : ℕ) (hk : 𝔤)
    (bar : 𝕺)
    (η : 𝖇) (x : 𝔮) : ℝ :=
  𝖊
    𝖔 x

𝗇 𝔄 𝗪₁
𝗇 𝔇 𝙖
𝗇 𝔈 𝘙
𝗇 𝕿 𝖶
𝗇 𝔛 Integrable (𝖑 x) 𝕿
𝗇 𝔜 𝖓 x.2 w
𝗇 𝔥 𝖓 x.1 w
𝗃 𝖅 ἀ C θ
𝗇 𝔰 𝖅 boundedPairRegressionOperator
𝗇 𝔷 PilotFields.pilotMean (M := 𝔄) bar η
𝗇 𝕬 ⟪ 𝔥, InnerProductSpace.rankOne ℝ 𝔈 𝔈 𝔜 ⟫
𝗇 𝖀 𝖞 pairPilotScoreMean
𝗇 𝕴 𝖀
𝗃 𝖂 ἀ C θ hθ k hk
𝗃 𝖄 ∫ w, ἀ ∂ 𝔄
theorem pairPilotScoreMean_eq_half_pilotMean C
    (θ : RegressionParameter d) (hθ : 𝖅 Admissible) k hk
    bar
    η (x : 𝔮)
    (hi : 𝔛) :
    𝕴 x = 𝔇 *
      𝔷
        𝔰 x := by
  let := 𝖅 observationLaw_isProbability hθ
  rw [pairPilotScoreMean, PairUStatistic.fieldPairMean]
  have h := 𝖅 pairScoreFieldKernel_mean hθ 𝔞
    𝔟 𝔚 hi
  unfold pairPilotScoreKernel
  rw [h]
  have hM := 𝖂 regularPairDesignMeasure_integral fun w =>
    𝕬
  calc
    _ = 𝔇 * (𝗋 * ∫ w, sameLabelKernel 𝖒 w *
      𝕬 ∂𝖱) := 𝖢₃
    _ = 𝔇 * 𝖄 𝕬 := by
      simp_all
    𝘿 := by
      congr 1
      apply integral_congr_ae
      filter_upwards [𝖂 boundedPairRegressionOperator_eq_ae] with w hw
      tauto

𝗇 𝔊 Integrable (𝖔 x) 𝕿
𝗃 𝖟 fun _ => ἀ
𝗇 𝔦 𝖟 pairNoiseOperator
𝗇 𝖁 𝖞 pairPilotNoiseMean
𝗇 𝕵 𝖁
theorem pairPilotNoiseMean_eq_half_pilotMean C
    (θ : RegressionParameter d) (hθ : 𝖅 Admissible) k hk
    bar
    η (x : 𝔮)
    (hi : 𝔊) :
    𝕵 x = 𝔇 *
      𝔷
        𝔦 x := by
  let := 𝖅 observationLaw_isProbability hθ
  rw [pairPilotNoiseMean, PairUStatistic.fieldPairMean]
  have h := 𝖅 pairNoiseFieldKernel_mean hθ 𝔞
    𝔟 𝔚 hi
  unfold pairPilotNoiseKernel
  rw [h]
  have hM := 𝖂 regularPairDesignMeasure_integral fun w =>
    ⟪ 𝔥, pairNoiseOperator 𝔜 ⟫
  simp only [smul_eq_mul, pairPilotCoefficient] at hM
  simp only [PilotFields.pilotMean, pairPilotCoefficient]
  linarith

𝗇 𝔍 𝘦₁
𝗇 𝖕 𝘭₂
𝗇 𝔒 fun z => 𝖕
𝗇 𝔲 𝖺
𝗃 𝖆 ∫ x, PilotFields.test (M := ἀ) η v x ^ 2 ∂μ
𝗇 𝖗 3 / 4 * lam
𝗃 𝖛 ∫ z, ἀ z ∂μ.prod μ
section HalfMean
variable {W H : Type*} [MeasurableSpace W]
variable [NormedAddCommGroup H] [𝗗₂] [CompleteSpace H]
𝛌
𝛕

𝗃 𝖜 ∫ w, ‖ἀ w‖ ^ 2 ∂M
𝗇 𝔉 ∀ v , MemLp v 2 M → 𝖆 M ≤ lam * 𝖜 v
𝗇 𝖈 PilotFields.pilotMean (M := M) bar η B
𝗇 𝔏 𝖈 x
𝗇 𝔑 ∀ w a b, ⟪a, B w b⟫ = ⟪B w a, b⟫
𝗇 𝔓 ∫ w, ⟪bar w, B w $ bar w ⟫ ∂M
𝗇 𝔘 Measurable fun z : 𝗶₁ => 𝖕
𝗇 𝔙 Measurable 𝚇
𝗇 𝔠 ∀ w, ‖B w‖ ≤ cB
𝗇 𝕰 MemLp 𝔒 2 $ μ.prod M
𝗇 𝕱 ∀ᵐ w ∂M, 𝔍
𝗃 𝖃 ἀ bar hbarMeas hbar hmη hη hcenter hmB hcB hlam hbound hsym htest
𝗇 𝖖 𝔇 * 𝔏
𝗃 𝖏 ∫ x, ἀ ∂μ.prod μ
theorem half_pilotMean_mean_eq bar (hbarMeas : Measurable bar) (hbar : MemLp bar 2 M)
    (hmη : 𝔘)
    (hη : 𝕰)
    (hcenter : 𝕱)
    (hmB : 𝔙)
    (hcB : 0 ≤ cB) (hlam : 𝔲) (hbound : 𝔠)
    (hsym : 𝔑)
    (htest : 𝔉) :
    𝖏 𝖖 =
      𝔇 * 𝔓 := by
  rw [integral_const_mul,
    𝖃 PilotFields.pilotMean_mean_eq]

𝗇 𝔎 𝖗 * cB ^ 2 * (2 * 𝖜 bar + ∫ z : 𝗶₁, ‖𝖕‖ ^ 2 ∂μ.prod M)
𝗇 𝔵 𝖈 z
𝗇 𝕭 (𝖖 - ∫ z, 𝔇 * 𝔵 ∂μ.prod μ) ^ 2
𝗃 𝖚 ἀ bar hbarMeas hbar hmη hη hmB hcB hlam hbound hsym htest
theorem half_pilotMean_centered_sq_le bar (hbarMeas : Measurable bar) (hbar : MemLp bar 2 M)
    (hmη : 𝔘)
    (hη : 𝕰)
    (hcenter : 𝕱)
    (hmB : 𝔙)
    (hcB : 0 ≤ cB) (hlam : 𝔲) (hbound : 𝔠)
    (hsym : 𝔑)
    (htest : 𝔉) :
    𝖏 𝕭 ≤
      𝔎 := by
  rw [𝖃 half_pilotMean_mean_eq]
  have he : (fun x => (𝖖 -
      𝔇 * 𝔓) ^ 2) =
       fun x => 𝚡 * (𝔏 -
        𝔓) ^ 2 := 𝖥₄
  rw [he, integral_const_mul]
  have h := mul_le_mul_of_nonneg_left
    𝖚 PilotFields.pilotMean_centered_sq_le
    (by norm_num : 𝙋 ≤ 𝚡)
  linarith

𝗇 𝔢 (G x - 𝖛 G) ^ 2
𝗃 𝔄₁ fun x => ἀ
theorem half_pilotMean_variance_transfer bar (hbarMeas : Measurable bar) (hbar : MemLp bar 2 M)
    (hmη : 𝔘)
    (hη : 𝕰)
    (hcenter : 𝕱)
    (hmB : 𝔙)
    (hcB : 0 ≤ cB) (hlam : 𝔲) (hbound : 𝔠)
    (hsym : 𝔑)
    (htest : 𝔉)
    G
    (he : G =ᵐ[μ.prod μ] 𝔄₁ 𝖖) :
    MemLp G 2 (μ.prod μ) ∧
      𝖏 𝔢 ≤
        𝔎 := by
  have hHalf := (𝖚 PilotFields.pilotMean_memLp_two).const_mul 𝔇
  refine ⟨hHalf.ae_eq he.symm, ?_⟩
  have hMean := integral_congr_ae he
  have hSq : 𝔄₁ 𝔢 =ᵐ[μ.prod μ]
      𝔄₁ 𝕭 := by
    filter_upwards [he] with x hx
    simp_all
  rw [integral_congr_ae hSq]
  exact 𝖃 half_pilotMean_centered_sq_le

end HalfMean

theorem pairNoiseOperator_symmetric a b :
    ⟪a, pairNoiseOperator b⟫ = ⟪pairNoiseOperator a, b⟫ := by
  rw [← real_inner_comm (pairNoiseOperator a) b, pairNoiseOperator_inner, pairNoiseOperator_inner]
  ring

𝗇 𝔖 ∫ x, 𝖁 x ∂μ.prod μ
𝗇 𝔗 𝖂 regularPairDesignMeasure_isFinite
𝗇 𝔧 𝖁
𝗇 𝔨 𝖟 pairNoiseOperator_norm_le
𝗇 𝔳 𝚌₂
𝗇 𝔶 ‖bar w‖
𝗇 𝔱 MemLp v 2 𝔄 → 𝖆 𝔄 ≤ lam * 𝖄 𝔳
𝗇 𝕮 ∀ᵐ x ∂μ.prod μ, 𝔊
𝗇 𝕲 ∀ᵐ w ∂ 𝔄, 𝔍
𝗇 𝕶 𝖕
𝗇 𝕷 ∀ᵐ w ∂ 𝔄, bar w 0 = 1
𝗇 𝕸 𝖂 pairPilotNoiseMean_eq_half_pilotMean bar η x hx
𝗇 𝕻 fun z : Ω × 𝔅 => 𝕶
𝗃 𝖝 fun x => 𝔇 * 𝔷 ἀ x
𝗇 𝕽 𝔧 =ᵐ[μ.prod μ] 𝖝 𝔦
𝗇 𝖉 ∀ᵐ w ∂ 𝔄, 𝔶 ≤ R
𝗇 𝖋 𝖟 pairNoiseOperator_symmetric
𝗇 𝖎 PilotFields.inner_integrable hbar hOp
section ActualMean
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : 𝖅 Admissible)
variable (k : ℕ) (hk : 𝔤) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (bar : 𝕺)
variable (η : 𝖇)
include C hθ

section

variable (hbarMeas : Measurable bar)
    (R)
    (hbarBound : 𝖉)

include hbarMeas hbarBound

𝗇 𝔣 bar w 0 ^ 2 + bar w 1 ^ 2
𝗇 𝖍 MemLp 𝔒 2 $ μ.prod 𝔄
theorem pairPilotNoiseMean_mean_eq
    (hmη : Measurable 𝕻)
    (hη : 𝖍)
    (hcenter : 𝕲)
    lam (hlam : 𝔲)
    (htest : ∀ v ,
      𝔱)
    (hi : 𝕮) :
    𝔖 =
      𝔇 * 𝖄 𝔣 := by
  let := 𝔗
  have he : 𝕽 := by
    filter_upwards [hi] with x hx
    exact 𝕸
  rw [integral_congr_ae he, half_pilotMean_mean_eq bar hbarMeas (MemLp.of_bound hbarMeas.aestronglyMeasurable R hbarBound) hmη hη hcenter
     𝖦₃   𝖠₄  hlam
    𝔨 𝖋 htest]
  simp only [pairNoiseOperator_inner, pow_two]

𝗇 𝕯 ∫ w, ⟪bar w, pairNoiseOperator $ bar w ⟫ ∂ 𝔄
theorem pairPilotNoiseMean_mean_lower
    (hfirst : 𝕷)
    (hmη : Measurable 𝕻)
    (hη : 𝖍)
    (hcenter : 𝕲)
    lam (hlam : 𝔲)
    (htest : ∀ v ,
      𝔱)
    (hi : 𝕮) :
    𝔇 ≤ 𝔖 := by
  let := 𝔗
  have hbar : MemLp bar 2 𝔄 :=
    MemLp.of_bound hbarMeas.aestronglyMeasurable R hbarBound
  have hOp := PilotFields.operatorField_memLp  𝖦₃ 
    𝔨 hbarMeas hbar
  have hLow : (𝔄).real univ ≤
      𝕯 := by
    have h := integral_mono_ae (integrable_const 1) 𝖎 $ by
      filter_upwards [hfirst] with w hw
      rw [pairNoiseOperator_inner, hw]
      nlinarith
    simp_all
  rw [𝖂 pairPilotNoiseMean_mean_eq μ bar η hbarMeas R hbarBound hmη hη hcenter lam hlam htest hi]
  have hEq : 𝖄 𝔣 =
      𝕯 := by
    simp only [pairNoiseOperator_inner, pow_two]
  linarith [(𝖂 regularPairDesignMeasure_mass_bounds).1]

end

end ActualMean

/-- Primitive measurable and moment conditions of the original two pilots.
No conditional mean, bias, variance, or statistical risk conclusion occurs
among these fields. -/
structure PairPilotMeanConditions {d : ℕ} (θ : RegressionParameter d) (k : ℕ) (hk : 𝔤)
    (μ : Measure Ω) (bar : 𝕺)
    (η : 𝖇) (R lam : ℝ) : Prop where
  barMeasurable : Measurable bar
  barBound : 𝖉
  noiseMeasurable : Measurable 𝕻
  noiseMemLp : MemLp 𝕻 2
    $ μ.prod 𝔄
  noiseCentered : 𝕲
  lamNonnegative : 𝔲
  linearTest : ∀ v : 𝕺,
    𝔱
  scoreConditionalIntegrable : ∀ᵐ x ∂μ.prod μ, 𝔛
  noiseConditionalIntegrable : 𝕮

section ConcreteBounds
variable {d : ℕ} (C : ModelConstants d) (θ : RegressionParameter d) (hθ : 𝖅 Admissible)
variable (k : ℕ) (hk : 𝔤) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (bar : 𝕺)
variable (η : 𝖇) (R lam : ℝ)
variable (hp : PairPilotMeanConditions θ k hk μ bar η R lam)
include C hθ hp

𝗇 𝔐 ∫ x, 𝖀 x ∂μ.prod μ
𝗇 𝔡 MemLp.of_bound hp.barMeasurable.aestronglyMeasurable R hp.barBound
𝗇 𝔩 ⟪bar w, 𝖅 boundedPairRegressionOperator w $ bar w ⟫
𝗇 𝔪 𝖀
𝗇 𝔫 𝖅 boundedPairRegressionOperator_measurable_apply hθ
𝗇 𝔴 𝖅 boundedPairRegressionOperator_norm_le
𝗇 𝕹 𝖂 pairPilotScoreMean_eq_half_pilotMean bar η x hx
𝗇 𝕾 𝔪 =ᵐ[μ.prod μ] 𝖝 𝔰
theorem pairPilotScoreMean_mean_eq :
    𝔐 =
      𝔇 * 𝖄 𝔩 := by
  let := 𝔗
  have he : 𝕾 := by
    filter_upwards [hp.scoreConditionalIntegrable] with x hx
    exact 𝕹
  rw [integral_congr_ae he]
  exact half_pilotMean_mean_eq bar hp.barMeasurable 𝔡 hp.noiseMeasurable hp.noiseMemLp hp.noiseCentered
    𝔫  𝖠₃  hp.lamNonnegative
    𝔴 𝖅 boundedPairRegressionOperator_symmetric hp.linearTest

𝗇 𝔬 𝘺
𝗃 𝖘 𝖂 ἀ μ bar η R lam hp
𝗇 𝔭 𝖘 pairPilotScoreMean_mean_eq
/-- The actual conditional numerator-minus-variance-denominator mean has
bias bounded by the squared pointwise deterministic residual. -/
theorem pairPilotScoreMean_bias_le b
    (hresidual : ∀ᵐ w ∂ 𝔄,
      |⟪bar w, 𝔈 ⟫| ≤ b) :
    𝔐 ≤ C.densityUpper / 2 * 𝔬 := by
  let := 𝔗
  have hbar : MemLp bar 2 𝔄 :=
    𝔡
  have hOp := PilotFields.operatorField_memLp 𝔫
    𝔴 hp.barMeasurable hbar
  have hPoint : (fun w => 𝔩) ≤ᵐ[𝔄]
      𝖟 𝔬 := by
    filter_upwards [𝖂 boundedPairRegressionOperator_eq_ae, hresidual] with w hw hr
    rw [hw, InnerProductSpace.inner_right_rankOne_apply,
      real_inner_comm (bar w) 𝔈]
    have hSq := 𝗂 hr 2
    rw [sq_abs] at hSq
    linarith
  have hUpper := integral_mono_ae 𝖎 (integrable_const 𝔬) hPoint
  simp at hUpper
  rw [𝔭]
  calc
    _ ≤ 𝔇 * ((𝔄).real univ * 𝔬) :=
      mul_le_mul_of_nonneg_left hUpper 𝖠₄
    _ ≤ 𝔇 * (C.densityUpper * 𝔬) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (𝖂 regularPairDesignMeasure_mass_bounds).2 $ sq_nonneg b )
      𝖠₄
    𝘿 := 𝖢₃

theorem pairPilotNoiseMean_denominator_lower
    (hfirst : 𝕷) :
    𝔇 ≤ 𝔖 :=
  𝖂 pairPilotNoiseMean_mean_lower μ bar η hp.barMeasurable R hp.barBound hfirst
    hp.noiseMeasurable hp.noiseMemLp hp.noiseCentered lam hp.lamNonnegative hp.linearTest hp.noiseConditionalIntegrable

𝗇 𝕳 2 * ∫ w, 𝔶 ^ 2 ∂ 𝔄
𝗇 𝕼 𝕳 + ∫ z : Ω × 𝔅, ‖𝕶‖ ^ 2 ∂μ.prod 𝔄
𝗇 𝖐 half_pilotMean_variance_transfer bar hp.barMeasurable 𝔡 hp.noiseMeasurable hp.noiseMemLp hp.noiseCentered
/-- Genuine L² integrability and variance of the actual numerator score mean.
The universal pilot tests provide the variance; no fourth pilot moment is used. -/
theorem pairPilotScoreMean_variance_le :
    MemLp 𝔪 2 (μ.prod μ) ∧
       ∫ x, (𝕴 x -
        𝖛 𝕴) ^ 2 ∂μ.prod μ ≤
      𝖗 * 𝗳₂ ^ 2 *
        𝕼 := by
  let := 𝔗
  have he : 𝕾 := by
    filter_upwards [hp.scoreConditionalIntegrable] with x hx
    exact 𝕹
  exact 𝖐
    𝔫  𝖠₃  hp.lamNonnegative
    𝔴 𝖅 boundedPairRegressionOperator_symmetric
    hp.linearTest _ he

theorem pairPilotNoiseMean_variance_le :
    MemLp 𝔧 2 (μ.prod μ) ∧
       ∫ x, (𝕵 x -
        𝖛 𝕵) ^ 2 ∂μ.prod μ ≤
      3 * lam * 𝕼 := by
  let := 𝔗
  have he : 𝕽 := by
    filter_upwards [hp.noiseConditionalIntegrable] with x hx
    exact 𝕸
  obtain ⟨hL2, hVar⟩ := 𝖐  𝖦₃ 
     𝖠₄  hp.lamNonnegative 𝔨
    𝖋 hp.linearTest _ he
  bound

𝗇 𝔔 pairResponseVector (𝖅 boundedRegression w.1) $ 𝖅 boundedRegression w.2
/-- The genuine conditional score mean is nonnegative because its
deterministic population operator is a positive rank-one form. -/
theorem pairPilotScoreMean_mean_nonneg :
    0 ≤ 𝔐 := by
  rw [𝔭]
  apply mul_nonneg 𝖠₄
  apply integral_nonneg
  intro w
  change 0 ≤ ⟪bar w, InnerProductSpace.rankOne ℝ
    𝔔
    𝔔 $ bar w ⟫
  rw [InnerProductSpace.inner_right_rankOne_apply,
    real_inner_comm (bar w)
      𝔔]
  exact mul_self_nonneg _

/-- The squared deterministic residual bounds the absolute actual score
mean, with no bias assumption on the pilot law. -/
theorem pairPilotScoreMean_abs_bias_le b
    (hresidual : ∀ᵐ w ∂ 𝔄,
      |⟪bar w, 𝔈 ⟫| ≤ b) :
    |𝔐| ≤
       C.densityUpper / 2 * 𝔬 := by
  rw [abs_of_nonneg 𝖘 pairPilotScoreMean_mean_nonneg]
  exact 𝖘 pairPilotScoreMean_bias_le b hresidual
