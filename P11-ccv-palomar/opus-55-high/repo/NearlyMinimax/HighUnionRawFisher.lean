module

public import NearlyMinimax.HighUnionFisher
public import NearlyMinimax.HighRawScoreEnergy
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The genuine spatial factorial budget yields joint raw Fisher
integrability and the mass-normalized energy for the actual source prior. -/
𝚫
𝚪
𝚨
𝛈
𝛀
𝚬
attribute [local irreducible] highUnionSourceDensity highUnionSourceRegression highUnionSourceState
  historyMarkedAppend highRawSampleLikelihood massPowerNormalizer

𝗇 𝔗 𝙯
𝗇 𝔈 𝔗 → 𝗖
𝗇 𝔉 Measure.pi fun _ : Fin r => 𝖪
/-- Exact spatial factorial series in the original normalized experiment. -/
def highSourceSpatialSeries (d k n : ℕ) [NeZero k] (pMinus cMass : ℝ)
    (H : 𝔈) : ℝ :=
  (𝚐 : ℕ)*∑ j : 𝔗, ∑ r ∈ Finset.range 𝗉,
    (𝙒*highFixedScoreDenominator pMinus cMass*(2/𝙦)^d)^r /
      (r.factorial : ℝ)*∫ u, H j r u
        ∂𝔉

variable {d k D : ℕ} {I : Type*} [Fintype I] {E : 𝗀}
    [𝙪] [𝖭]
    [NeZero k] [LinearOrder 𝔗]
    (C : ModelConstants d) (R : 𝙭₁ I E)
    {M Cfr : ℝ} (G : 𝗗)
    (hpos : 𝚣)

𝗇 𝔍 𝗘₁
𝗇 𝔎 𝗛
𝗇 𝔏 𝗾
𝗇 𝔐 𝖫
𝗇 𝔄 highHistoryLikelihoodDerivative 𝔐 𝔍 𝔎 𝔏 n a V η
𝗃 𝔙 fun h => highRawDensityMass $ ἀ h
𝗇 𝔅 massPowerNormalizer ν 𝔙 p n
𝗇 𝔇 𝔐
𝗇 𝔊 highUnionSourceRegression C R η
𝗇 𝔑 H h j r
𝗇 𝔒 highUnionSourceDensity C R
𝗇 𝔓 D z.1 z.2 ^ 2 / L z.1 z.2
𝗇 𝔔 HistoryMarked 𝔇 $ HighUnionMark E
𝗇 𝔖 ν.prod 𝘱
𝗃 𝔘 ἀ C R G
include G hpos in
 theorem highUnionSource_raw_fisher_bound
    (ν : Measure 𝔔)
    [IsProbabilityMeasure ν] (n : ℕ) (hk : 𝗑)
    (a V η cMass : ℝ) (ha : 𝙞) (hcMass : 0 < cMass)
    (hq : ∀ h x y, cMass ≤ ternaryMass a (𝔊 h x) V y)
    (hDensity : ∀ j h (x : 𝙇),
       ∫ e, 𝔏 e *
        ∏ i, 𝘖₁ e (x i) ∂𝔎 = 0)
    (H : 𝔔 →
      𝔈)
    (hH : ∀ h j r, Integrable 𝔑
      𝔉)
    (hH0 : ∀ h j r u, 0 ≤ 𝔑 u)
    (hdom : ∀ h j r x, (∀ i, x i ∈ 𝘋) →
      selectedRawSquareEnergy (highUnionSourceRawNumerator C R r a V η h j) x ≤
        𝔑 (highPatchProductChart d k j x))
    (B : ℝ) (hB : 𝙐)
    (hbudget : ∀ h, highSourceSpatialSeries d k n C.densityLower cMass (H h) ≤ B) :
    let D := 𝔄 𝔒 𝔊
    let L := fun h => highRawSampleLikelihood n a V
      (𝔒 h) $ 𝔊 h
    let m := 𝔙 𝔒
    Integrable (fun z => 𝔓) 𝔖 ∧
    𝖡₁⁻¹ *
       ∫ z, 𝔓 ∂𝔖 ≤ B := by
  letI : 𝗄₁ := highUnionMark_standardBorel
  letI := 𝔘 highUnionSourceLaw_probability
  let p := 𝔒
  let F := 𝔊
  have hp : 𝘍 := 𝔘 highUnionSourceDensity_joint_measurable
  have hF : 𝗴 := 𝔘 highUnionSourceRegression_joint_measurable η
  let D := 𝔄 p F
  have hDm : Measurable $ Function.uncurry D := highHistoryLikelihoodDerivative_measurable
    𝔇
    𝔍
    𝔎 𝔏
    (highUnionActivation_measurable R G.activation_measurable _) n a V η p F hp hF
  have hs h := 𝔘 highUnionSource_sample_fisher_bound hpos n hk a V η cMass ha hcMass
    hq hDensity h (H h) (hH h) (hH0 h) $ hdom h
  have hj := high_raw_joint_fisher_integrable_bound ν n a V p F hp hF
    C.densityLower C.densityUpper C.densityLower_pos
    𝔘 highUnionSourceDensity_coarse_interval (fun h x y => hcMass.trans_le $ hq h x y )
    D hDm B hB
     fun h => by simpa only [highHistoryLikelihoodScore] using (hs h).1
     fun h => by
      have hb0 := hbudget h
      unfold highSourceSpatialSeries at hb0
      have hb := (hs h).2.trans hb0
      simpa only [highHistoryLikelihoodScore] using hb
  have hG : 0 < 𝔅 :=
    massPowerNormalizer_pos ν _ 𝙨 n
      C.densityLower C.densityUpper C.densityLower_pos
       fun h => highRawDensityMass_mem_Icc (p h) hp.of_uncurry_left
        C.densityLower C.densityUpper C.densityLower_pos
        $ Filter.Eventually.of_forall $ 𝔘 highUnionSourceDensity_coarse_interval h
  refine ⟨hj.1, ?_⟩
  calc
    _ ≤ 𝔅⁻¹ *
        (𝔅 * B) :=
      mul_le_mul_of_nonneg_left hj.2 $ inv_nonneg.mpr hG.le
    _ = B := by rw [← mul_assoc, inv_mul_cancel₀ hG.ne', one_mul]
