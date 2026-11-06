module

public import NearlyMinimax.PaperPairRisk
public import NearlyMinimax.SampleThirds
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! A Borel pair estimator constructed directly from observable coefficient
fields, with its actual original-sample risk and minimax comparison. -/
𝚵
open scoped ENNReal RealInnerProductSpace
𝚨
𝚩
𝛃
𝚰

𝗇 𝔅 𝙩
𝗇 𝔊 𝗰
𝗇 𝔎 regularObservationLabel k hk
𝗇 𝔑 𝚎
𝗇 𝔖 𝖰
𝗇 𝔗 pairResponseVector z.1.2 z.2.2
𝗃 𝔛 c ἀ $ pairCovariates z
def coefficientPairNumeratorKernel (k : ℕ) (hk : 𝔖)
    (c : Ω → 𝔅 → PairVector) (p : 𝔑)
    (z : 𝔊) : ℝ :=
  sameLabelKernel 𝔎 z *
    ⟪𝔛 p.1, InnerProductSpace.rankOne ℝ
      𝔗 𝔗
        𝔛 p.2⟫

𝗃 𝔙 Measurable fun z : ἀ × 𝔅 => c z.1 z.2
theorem coefficientPairNumeratorKernel_measurable [MeasurableSpace Ω]
    (k : ℕ) (hk : 𝔖)
    (hmc : 𝔙 Ω) :
    Measurable fun z : 𝔑 × 𝔊 =>
      coefficientPairNumeratorKernel k hk c z.1 z.2 := by
  have hm := PilotFields.maskedPilotKernel_measurable
    (c := fun x z => 𝔛 x)
    (A := fun z => pairScoreOperator 0 z.1.2 z.2.2)

    (pilotOnObservations_measurable hmc)
    (observationPairScoreOperator_measurable_apply 0)
    $ sameLabelKernel_measurable 𝔎
      $ regularObservationLabel_measurable k hk
  change Measurable fun z : 𝔑 × 𝔊 =>
    sameLabelKernel 𝔎 z.2 *
      ⟪c z.1.1 $ pairCovariates z.2 , pairScoreOperator 0 z.2.1.2 z.2.2.2
        $ c z.1.2 $ pairCovariates z.2 ⟫ at hm
  simpa only [coefficientPairNumeratorKernel, pairScoreOperator,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, zero_smul, sub_zero] using hm

𝗇 𝔄 Fin m → Observation d
𝗇 𝔇 fun i x => x i
𝗇 𝔉 𝚡
𝗇 𝔏 𝙦 ^ d
𝗃 𝔚 PairUStatistic.fieldPairAverage m 𝔏 (ἀ k hk c) 𝔇
def coefficientPairStatistic (C : ModelConstants d) (m k : ℕ) (hk : 𝔖)
    (c : 𝔄 → 𝔅 → PairVector)
    (z : (𝔄 × 𝔄) × 𝔄 ) : ℝ :=
  stabilizedRatio C.varianceLower C.varianceUpper 𝔉
    𝔚 coefficientPairNumeratorKernel
    𝔚 rawModelPairNoise z

𝗇 𝔐 fun i (x : 𝔄) => x i
𝗇 𝔘 𝗋
𝗃 𝔜 PairUStatistic.fieldPairAverage_measurable m 𝔘 (ἀ k hk hmc) 𝔐 measurable_pi_apply
theorem coefficientPairStatistic_measurable {d } C m k
    hk {c }
    (hmc : 𝔙 𝔄) :
    Measurable $ coefficientPairStatistic C m k hk c := by
  have hN :=
    𝔜 coefficientPairNumeratorKernel_measurable
  have hD :=
    𝔜 rawModelPairNoise_measurable
  exact stabilizedRatio_measurable C.varianceLower C.varianceUpper 𝔉 hN hD

𝗇 𝔍 Fin $ threeBlockSize n
𝗇 𝔔 𝔍 → Observation d
def coefficientPairEstimator {d n : ℕ} (C : ModelConstants d) (k : ℕ) (hk : 𝔖)
    (c : 𝔔 → 𝔅 → PairVector)
    (hmc : 𝔙 𝔔) : 𝚠 :=
  threeBlockEstimator (coefficientPairStatistic C (threeBlockSize n) k hk c)
    $ coefficientPairStatistic_measurable C _ k hk hmc

𝗇 𝔈 sampleLaw θ $ threeBlockSize n
𝗇 𝔒 𝙖
𝗇 𝔓 fun _ : 𝔍 => observationLaw θ
/-- Independent pilots and evaluation data arise from the original iid sample;
the coefficient field is observable and carries no unknown parameter. -/
theorem coefficientPairEstimator_rms_bound C
    (θ : RegressionParameter d) (hθ : 𝙟) (hn : 6 ≤ n)
    k hk
    c
    hmc
    bar
    η
    Cp W b (heq : c = pairPilotCoefficient bar η)
    (hp : PairPilotAssumptions θ k hk 𝔈 bar η
      Cp W 𝗽₂)
    (hfirst : ∀ᵐ w ∂𝗪₁, bar w 0 = 1)
    (hresidual : ∀ᵐ w ∂𝗪₁,
      |⟪bar w, 𝘙⟫| ≤ b) :
    meanSquaredRisk (coefficientPairEstimator C k hk c hmc) θ ^ (𝔒 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt (pairRateSquaredConstant C Cp 𝔉 𝔉) *
        (𝘺 + 𝖨₂ k * 𝚢₂)) := by
  let := 𝙱
  let := sampleLaw_isProbability C θ hθ $ threeBlockSize n
  have hi := iIndepFun_pi (μ := 𝔓)
      fun _ => aemeasurable_id
  have h := paper_common_pair_rms 𝔈 𝔈
    C θ hθ k hk bar η Cp W  𝖡₃  (threeBlockSize_two_le hn)
     𝖠₄  (threeBlockSize_fraction hn) hp hfirst
    𝔇 hi (measurePreserving_eval 𝔓) b hresidual
  unfold coefficientPairEstimator
  rw [threeBlockEstimator_risk_eq C θ hθ]
  bound

theorem minimaxRMS_le_of_estimator_rms C
    (T : 𝚠)
    (hT : ∀ θ , 𝙟 → meanSquaredRisk T θ ^ (𝔒 : ℝ) ≤ B) :
    𝚢 ≤ B := by
  have h := ENNReal.rpow_le_rpow (minimaxRisk_le_worstCaseRisk C T)
    (by norm_num : 𝙋 ≤ 𝔒)
  apply h.trans
  let φ := ENNReal.orderIsoRpow 𝔒 𝖠₄
  change φ (⨆ θ : {θ : RegressionParameter d // 𝙟}, meanSquaredRisk T θ.val) ≤ B
  simpa
