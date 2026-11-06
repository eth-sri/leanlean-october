module

public import NearlyMinimax.HighMarginalLikelihood
public import NearlyMinimax.HighResponseDecoding
public import NearlyMinimax.WeightedScoreContraction
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The actual observed-data score: the averaged genuine likelihood derivative
 divided by the averaged genuine likelihood. -/
𝚹
𝚮
𝚨
𝚭
𝚩
𝚲

𝗇 𝔄 𝘼
𝗇 𝔤 𝙗
𝗇 𝔇 𝔤 → 𝙀
𝗇 𝔈 Measure 𝔤
𝗇 𝔉 𝙁
𝗇 𝔙 𝙇 × 𝙈
𝗇 𝔒 𝔙
𝗇 𝔔 𝙏
𝗇 𝔞 𝗿₁ V η p F
def highMarginalLikelihoodDerivative [MeasurableSpace E]
    (dependent : 𝔉) (hsymm : 𝔄)
    (ν : 𝔈) (π : Measure E) (activation : 𝔔)
    (n : ℕ) (a V η : ℝ) (p F : 𝔇)
    (z : 𝔒) : ℝ :=
  ∫ ω, 𝔞 ω z ∂ν

𝗃 𝔟 ἀ dependent hsymm ν π activation
𝗃 𝔥 𝔟 ἀ n a V η p F
𝗇 𝔖 𝔥 highMarginalLikelihoodDerivative z
𝗃 𝔧 ἀ ν n a V p F
𝗇 𝔡 𝔧 highMarginalRawLikelihood z
def highMarginalIndexScore [MeasurableSpace E]
    (dependent : 𝔉) (hsymm : 𝔄)
    (ν : 𝔈) (π : Measure E) (activation : 𝔔)
    (n : ℕ) (a V η : ℝ) (p F : 𝔇)
    (z : 𝔒) : ℝ :=
  𝔖 /
    𝔡

𝗇 𝔛 𝔥 highMarginalIndexScore
def highMarginalRealScore [MeasurableSpace E]
    (dependent : 𝔉) (hsymm : 𝔄)
    (ν : 𝔈) (π : Measure E) (activation : 𝔔)
    (n : ℕ) (a V η : ℝ) (p F : 𝔇)
    (z : 𝙌) : ℝ :=
  𝔛 $ decodeDesignResponse a z

𝗇 𝔎 𝚂₂
𝗇 𝔗 𝔧 highMarginalRawLikelihood_measurable hp hF
𝗃 𝔨 Measurable $ Function.uncurry ἀ
theorem highMarginalIndexScore_measurable [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔉) (hsymm : 𝔄)
    (ν : 𝔈) [SFinite ν] (π : Measure E) [SFinite π]
    (activation : 𝔔) (ham : Measurable activation) (n : ℕ) (a V η : ℝ)
    (p F : 𝔇)
    (hp : 𝔨 p) (hF : 𝔨 F) :
    Measurable 𝔛 := (𝔎).stronglyMeasurable.integral_prod_left'.measurable.div
    𝔗

𝗇 𝔜 𝔥 highMarginalRealScore
𝗃 𝔦 𝔟 ἀ ham n a V η p F hp hF
theorem highMarginalRealScore_measurable [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔉) (hsymm : 𝔄)
    (ν : 𝔈) [SFinite ν] (π : Measure E) [SFinite π]
    (activation : 𝔔) (ham : Measurable activation) (n : ℕ) (a V η : ℝ)
    (p F : 𝔇)
    (hp : 𝔨 p) (hF : 𝔨 F) :
    Measurable 𝔜 :=
  (𝔦 highMarginalIndexScore_measurable).comp
    $ decodeDesignResponse_measurable a

𝗇 𝔘 𝙽₂ * 𝔞 z.1 z.2
𝗇 𝔚 𝙙
𝗇 𝔣 𝘱
𝗇 𝔅 (massPowerNormalizer ν 𝔚 n)⁻¹ * ∫ z : 𝔤 × 𝔙, 𝔘 ∂ν.prod 𝔣
𝗇 𝔊 𝔘
𝗇 𝔍 𝔚
𝗇 𝔏 ∀ ω x y, 0 < 𝙅 V y
𝗇 𝔐 fun ω x y => (hq ω x y).le
𝗇 𝔓 𝙄
𝗃 𝔠 ἀ n a V p F hp hF ∘ₘ massPowerTilt ν 𝔍 n
𝗇 𝔢 𝗟₁
/-- Actual marginal score testing has the genuine averaged derivative
as its density; all Fubini integrability is derived from primitive bounds. -/
theorem highMarginalIndexScore_integral [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔉) (hsymm : 𝔄)
    (ν : 𝔈) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝔔) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 𝙑) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η aRaw bRaw B : ℝ) (ha : 𝙆) (haRaw : 𝙓) (hB : 𝙐)
    (p F : 𝔇)
    hp hF
    (hraw : 𝔓)
    (hq : 𝔏)
    H (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
     ∫ z, H 𝔢 *
      𝔛 z
      ∂𝔠 highSampleIndexKernel =
      𝔅 := by
  let m := 𝔍
  have hb ω :=
    𝙕
  have hG := massPowerNormalizer_pos ν m 𝙨 n aRaw bRaw haRaw hb
  have hpb ω x : |𝗃₁| ≤ |bRaw| := by
    grind
  have hL z := highMarginalRawLikelihood_pos ν n a V |bRaw| (abs_nonneg _) ha.ne' p F hp hF
    (fun ω x => haRaw.trans_le (hraw ω x).1) hpb hq z
  have hdens : Measurable fun z => ENNReal.ofReal
      $ 𝔡 / 𝖡₁ :=
    ((𝔗).div_const _).ennreal_ofReal
  rw [𝔧 highMassTilt_index_marginal_density hp hF aRaw bRaw haRaw ha.ne' hraw
    𝔐,
    integral_withDensity_eq_integral_toReal_smul hdens $ Eventually.of_forall 𝘕 ]
  simp_rw [ENNReal.toReal_ofReal $ div_nonneg (hL _).le hG.le , smul_eq_mul]
  have hi : Integrable (fun z =>
      𝔊)
      $ ν.prod 𝔣 := by
    apply Integrable.of_bound
      (𝙢
        𝔎).aestronglyMeasurable
      $ B * ( Fintype.card J * (Ba * |bRaw|^n) + 𝙎 * (|bRaw|^n * (n/𝗅)))
    exact Eventually.of_forall fun z => by
      change ‖𝔊‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact 𝘣 (highHistoryLikelihoodDerivative_abs_le π dependent hsymm activation Ba hBa
        habound n a V η |bRaw| (abs_nonneg _) ha p F hpb 𝔐 z.1 z.2)
        (abs_nonneg _) hB
  calc
    _ = 𝖡₁⁻¹ *
        ∫ z, H 𝔢 *
          𝔖
          ∂𝔣 := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only [highMarginalIndexScore]
        grind
    𝘿 := by
      congr 1
      rw [MeasureTheory.integral_prod_symm _ hi]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only [highMarginalLikelihoodDerivative]
        rw [integral_const_mul]

𝗇 𝔑 H z * 𝔜 z
theorem highMarginalRealScore_integral [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔉) (hsymm : 𝔄)
    (ν : 𝔈) [IsProbabilityMeasure ν]
    (π : Measure E) [IsProbabilityMeasure π] (activation : 𝔔) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 𝙑) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η aRaw bRaw B : ℝ) (ha : 𝙆) (haRaw : 𝙓) (hB : 𝙐)
    (p F : 𝔇)
    hp hF
    (hraw : 𝔓)
    (hq : 𝔏)
    H (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
     ∫ z, 𝔑
      ∂𝔠 highRealSampleKernel =
      𝔅 := by
  have hm : Measurable fun z => 𝔑 :=
    hH.mul 𝔦 highMarginalRealScore_measurable
  rw [highRealSampleKernel, ← Measure.map_comp _ _ $ encodeDesignResponse_measurable a ,
    integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) hm.stronglyMeasurable]
  have he := 𝔟 highMarginalIndexScore_integral ham Ba hBa habound
    n a V η aRaw bRaw B ha haRaw hB p F hp hF hraw hq H hH hHb
  convert he using 1
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only [highMarginalRealScore]
    rw [decodeDesignResponse_encode a ha]
