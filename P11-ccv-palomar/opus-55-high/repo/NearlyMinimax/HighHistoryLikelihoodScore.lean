module

public import NearlyMinimax.HighAppendLikelihood
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! The genuine likelihood score of the constructed marked-history experiment.
The derivative numerator uses actual append likelihood actions and one variance
heat correction. This module does not assume a score derivative identity. -/
𝚹
𝚨
𝚭
𝚩
𝚲

𝗇 𝔄 𝙇 × 𝙈
𝗇 𝔅 𝘼
𝗇 𝔉 𝙗 → 𝙀
𝗃 𝔥 ἀ dependent hsymm π activation n a V
𝗇 𝔊 ∑ j, 𝔥 highAppendLikelihoodAction p F j ω z
𝗇 𝔏 𝙁
𝗇 𝔠 𝙎
𝗃 𝔮 ἀ n a V
𝗃 𝔤 𝔮 ἀ (p ω) $ F ω
𝗇 𝔐 𝔠 * 𝔤 highRawSampleVarianceDerivative z
𝗇 𝔖 𝙗
𝗇 𝔦 𝙏
def highHistoryLikelihoodDerivative [MeasurableSpace E]
    (dependent : 𝔏) (hsymm : 𝔅)
    (π : Measure E) (activation : 𝔦) (n : ℕ) (a V η : ℝ)
    (p F : 𝔉)
    (ω : 𝔖) (z : 𝔄) : ℝ :=
  𝔊 -
    𝔐

𝗇 𝔗 𝔥 highHistoryLikelihoodDerivative η p F ω z
𝗇 𝔘 𝔤 highRawSampleLikelihood z
/-- A true score: the actual derivative numerator divided by the raw likelihood. -/
def highHistoryLikelihoodScore [MeasurableSpace E]
    (dependent : 𝔏) (hsymm : 𝔅)
    (π : Measure E) (activation : 𝔦) (n : ℕ) (a V η : ℝ)
    (p F : 𝔉)
    (ω : 𝔖) (z : 𝔄) : ℝ :=
  𝔗 /
    𝔘

𝗇 𝔒 𝙾₂
𝗇 𝔙 𝔥 highHistoryLikelihoodDerivative η p F z.1 z.2
𝗇 𝔜 𝔮 highRawSampleVarianceDerivative_joint_measurable p F hp hF
𝗃 𝔭 Measurable $ Function.uncurry ἀ
theorem highHistoryLikelihoodDerivative_measurable [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔏) (hsymm : 𝔅)
    (π : Measure E) [SFinite π] (activation : 𝔦) (ham : Measurable activation)
    (n : ℕ) (a V η : ℝ) (p F : 𝔉)
    (hp : 𝔭 p) (hF : 𝔭 F) :
    Measurable fun z : 𝔖 × 𝔄 =>
      𝔙 := (Finset.measurable_sum _ fun j _ =>
    𝔒 ).sub
      $ (𝔜).const_mul 𝔠

𝗇 𝔑 𝙅 V y
theorem highRawSampleLikelihood_pos n a V
    (p F : Ω → 𝙀) (hp : ∀ ω x, 0 < 𝗃₁)
    (hq : ∀ ω x y, 0 < 𝔑)
    ω z :
    0 < 𝔘 :=
  Finset.prod_pos fun i _ => mul_pos (hp ω _) $ hq ω ..

𝗇 𝔫 𝙯₁ z
𝗇 𝔇 ∑ j, ∫ z : 𝙗 × E, 𝔮 highRawObservable (p 𝔫) (F 𝔫) H * activation z.2 ∂ν.prod π
𝗇 𝔍 ∫ ω, 𝔤 highRawObservableVarianceDerivative H ∂ν
𝗇 𝔢 test z * A j z
𝗇 𝔎 ∑ j, ∫ z, 𝔢 ∂μ
𝗇 𝔓 𝙽₂
𝗇 𝔔 test z * D z
𝗇 𝔚 𝔥 highAppendLikelihoodAction p F j z.1 z.2
𝗇 𝔛 𝔮 highRawSampleVarianceDerivative (p z.1) (F z.1) z.2
𝗇 𝔞 fun j _ => hiA j
𝗇 𝔟 𝚗 * (n/𝗅)
𝗇 𝔡 Ba * 𝚗
𝗇 𝔣 highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa habound n a V P hP ha.ne' p F hpb hq j
𝗇 𝔧 ∀ ω x y, 0 ≤ 𝔑
𝗇 𝔨 ∫ z, 𝔔 ∂μ
𝗇 𝔩 𝘱
𝗇 𝔪 𝔮 highRawSampleVarianceDerivative_abs_le P ha hP
𝗃 𝔬 fun z => ἀ
/-- Integrability and Fubini for the actual score numerator derive from
bounded primitive likelihoods, including all reset states. -/
theorem highHistoryLikelihoodDerivative_observable [MeasurableSpace E]
    [StandardBorelSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (dependent : 𝔏) (hsymm : 𝔅)
    (ν : Measure 𝔖) [IsProbabilityMeasure ν]
    (activation : 𝔦) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 𝙑) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η P B : ℝ) (hP : 𝚏) (hB : 𝙐) (ha : 𝙆)
    (p F : 𝔉)
    (hp : 𝔭 p) (hF : 𝔭 F)
    (hpb : ∀ ω x, |𝗃₁| ≤ P) (hq : 𝔧)
    H (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B) :
     ∫ z : 𝔖 × 𝔄,
      𝔓 *
        𝔙
      ∂ν.prod 𝔩 =
       -𝔠 * 𝔍 +
        𝔇 := by
  let Q := 𝔖 × 𝔄
  let μ := ν.prod 𝔩
  let test : Q → ℝ := 𝔬 𝔓
  let A : J → Q → ℝ := fun j z =>
    𝔚
  let D : Q → ℝ := 𝔬 𝔛
  have htest : Measurable test := (hH.comp $ encodeDesignResponse_measurable a ).comp measurable_snd
  have hiA (j : J) : Integrable 𝔬 𝔢 μ := by
    apply Integrable.of_bound (htest.mul
      𝔒).aestronglyMeasurable
      $ B * 𝔡
    exact Eventually.of_forall fun z => by
      change ‖𝔓 *
        𝔚‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact 𝘣 (𝔣 z.1 z.2) (abs_nonneg _) hB
  have hiD : Integrable 𝔬 𝔔 μ := by
    apply Integrable.of_bound (htest.mul
      𝔜).aestronglyMeasurable
      $ B * 𝔟
    exact Eventually.of_forall fun z => by
      change ‖𝔓 * 𝔛‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul]
      exact 𝘣 (𝔪 _ _ (hpb _) (hq _) z.2)
        (abs_nonneg _) hB
  have heD : 𝔨 =
      𝔍 := MeasureTheory.integral_prod _ hiD
  calc
    _ = ∫ z, ∑ j, 𝔢 - 𝔠 * 𝔔 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp only [highHistoryLikelihoodDerivative, D]
        rw [mul_sub, Finset.mul_sum]
        ring
    _ = 𝔎 - 𝔠 * 𝔨 := by
      rw [integral_sub (integrable_finsetSum _ 𝔞) $ hiD.const_mul _ ,
        integral_finsetSum _ 𝔞, integral_const_mul]
    𝘿 := by
      rw [heD]
      have heA (j : J) := highAppendLikelihoodAction_prior_observable π dependent hsymm ν
        activation ham Ba hBa habound n a V P B hP hB ha.ne' p F hp hF hpb hq H hH hHb j
      have hs : 𝔎 =
          𝔇 := by
        aesop
      linarith

𝗇 𝔈 Fintype.card J * 𝔡 + 𝔠 * 𝔟
theorem highHistoryLikelihoodDerivative_abs_le [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π]
    (dependent : 𝔏) (hsymm : 𝔅)
    (activation : 𝔦) (Ba : ℝ) (hBa : 𝙑) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V η P : ℝ) (hP : 𝚏) (ha : 𝙆)
    (p F : 𝔉)
    (hpb : ∀ ω x, |𝗃₁| ≤ P) (hq : 𝔧)
    ω z :
    |𝔗| ≤
      𝔈 := by
  unfold highHistoryLikelihoodDerivative
  calc
    _ ≤ |𝔊| +
        |𝔐| := by
      grind
    _ ≤ 𝔈 := by
      apply add_le_add
      · refine 𝘡 ?_
        calc
          _ ≤ ∑ j : J, 𝔡 := Finset.sum_le_sum fun j _ =>
            𝔣 ω z
          𝘿 := 𝖢₄
      · rw [abs_mul, 𝚓₁]
        exact mul_le_mul_of_nonneg_left (𝔪
          (p ω) (F ω) (hpb ω) (hq ω) z) $ sq_nonneg η
