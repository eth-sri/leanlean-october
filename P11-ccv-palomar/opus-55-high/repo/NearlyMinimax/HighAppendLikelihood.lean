module

public import NearlyMinimax.HighTiltedObservable
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! The genuine append likelihood action and its Fubini observable bridge. -/
𝚹
𝚨
𝚭
𝚩
𝚲

𝗇 𝔛 𝙯₁
𝗇 𝔄 𝔛 (ω,e)
𝗇 𝔅 𝙇 × 𝙈
𝗇 𝔇 𝘼
𝗇 𝔊 𝙗 → 𝙀
𝗇 𝔐 𝙁
𝗇 𝔒 𝙗
𝗃 𝔥 ἀ n a V
𝗃 𝔦 𝔥 ἀ (p 𝔄) $ F 𝔄
𝗇 𝔘 𝔦 highRawSampleLikelihood z
𝗇 𝔞 𝙏
/-- Activation-weighted raw likelihood after the actual canonical marked append. -/
def highAppendLikelihoodAction [MeasurableSpace E]
    (dependent : 𝔐) (hsymm : 𝔇)
    (π : Measure E) (activation : 𝔞) (n : ℕ) (a V : ℝ)
    (p F : 𝔊) (j : J)
    (ω : 𝔒) (z : 𝔅) : ℝ :=
  ∫ e, activation e * 𝔘 ∂π

𝗇 𝔜 highAppendLikelihoodAction dependent hsymm π activation n a V p F j
𝗇 𝔎 𝔜 z.1 z.2
𝗇 𝔑 (𝔥 highRawSampleLikelihood_joint_measurable p F hp hF).comp hcoord
𝗇 𝔟 𝘍
𝗇 𝔠 𝗴
𝗇 𝔡 historyMarkedAppend_measurable dependent hsymm j
𝗇 𝔣 𝔒 × 𝔅
theorem highAppendLikelihoodAction_measurable [MeasurableSpace E]
    [StandardBorelSpace E]
    (dependent : 𝔐) (hsymm : 𝔇)
    (π : Measure E) [SFinite π] (activation : 𝔞) (ha : Measurable activation) (n : ℕ) (a V : ℝ)
    (p F : 𝔊)
    (hp : 𝔟) (hF : 𝔠) j :
    Measurable fun z : 𝔣 =>
      𝔎 := by
  have hcoord : Measurable fun z :
      𝔣 × E =>
      (𝔛 (z.1.1,z.2),z.1.2) :=
    ((𝔡).comp
      𝘙₂).prodMk
      $ measurable_snd.comp measurable_fst
  have hj :=
    (ha.comp measurable_snd).mul
      𝔑
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

𝗇 𝔉 ∀ ω x y, 0 ≤ 𝙅 V y
𝗇 𝔓 𝔜 ω z
𝗇 𝔖 Ba * 𝚗
theorem highAppendLikelihoodAction_abs_le [MeasurableSpace E]
    (π : Measure E) [IsProbabilityMeasure π]
    (dependent : 𝔐) (hsymm : 𝔇)
    (activation : 𝔞) (Ba : ℝ) (hBa : 𝙑) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V P : ℝ) (hP : 𝚏) (ha : 𝙞)
    (p F : 𝔊)
    (hp : ∀ ω x, |𝗃₁| ≤ P) (hq : 𝔉)
    j ω z :
    |𝔓| ≤ 𝔖 := by
  rw [highAppendLikelihoodAction, ← Real.norm_eq_abs]
  have hb : ∀ e, ‖activation e * 𝔘‖ ≤ 𝔖 := by
    intro e
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (habound e) (𝔥 highRawSampleLikelihood_abs_le P hP
      (p 𝔄)
      (F 𝔄)
      (hp _) ha (hq _) z) (abs_nonneg _) hBa
  simpa using norm_integral_le_of_norm_le_const (μ := π) $ Eventually.of_forall hb


𝗇 𝔙 𝔛 (ω,z.1)
𝗇 𝔚 𝙽₂
𝗇 𝔈 activation z.1 * (𝔚 * 𝔥 highRawSampleLikelihood (p 𝔙) (F 𝔙) z.2)
𝗇 𝔏 𝘱
𝗇 𝔔 𝙢
𝗇 𝔗 H 𝗟₁
𝗇 𝔢 activation e * (𝔗 * 𝔘)
𝗇 𝔤 B * 𝚗
/-- Fubini converts the true append action on a data observable into the
actual append likelihood action; integrability follows from the source bounds. -/
theorem highAppendLikelihoodAction_observable [MeasurableSpace E]
    [StandardBorelSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (dependent : 𝔐) (hsymm : 𝔇)
    (activation : 𝔞) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 𝙑) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V P B : ℝ) (hP : 𝚏) (hB : 𝙐) (ha : 𝙞)
    (p F : 𝔊)
    (hp : 𝔟) (hF : 𝔠)
    (hpb : ∀ ω x, |𝗃₁| ≤ P) (hq : 𝔉)
    H (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B)
    j ω :
     ∫ e, activation e * 𝔦 highRawObservable H ∂π =
      ∫ z, 𝔗 *
        𝔓
          ∂𝔏 := by
  have hcoord : Measurable fun z : E × 𝔅 =>
      (𝔙,z.2) :=
    ((𝔡).comp
      $ measurable_const.prodMk measurable_fst ).prodMk measurable_snd
  have hM : Measurable fun z : E × 𝔅 =>
      𝔈 :=
    (ham.comp measurable_fst).mul
      $ 𝔔
        𝔑
  have hi : Integrable (fun z =>
      𝔈)
      $ π.prod 𝔏 := by
    apply Integrable.of_bound hM.aestronglyMeasurable $ Ba * 𝔤
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      exact mul_le_mul (habound _) (𝘣 (𝔥 highRawSampleLikelihood_abs_le P hP
        _ _ (hpb _) ha (hq _) z.2) (abs_nonneg _) hB)  𝖠₃  hBa
  calc
    _ = ∫ e, ∫ z, 𝔢 ∂𝔏 ∂π := by
      simp_rw [highRawObservable, integral_const_mul]
    _ = ∫ z, ∫ e, 𝔢 ∂π ∂𝔏 :=
      integral_integral_swap hi
    𝘿 := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        dsimp
        rw [highAppendLikelihoodAction, ← integral_const_mul]
        grind

𝗃 𝔧 ἀ $ 𝔛 z
𝗇 𝔍 𝔥 highRawObservable 𝔧 p 𝔧 F H * activation z.2
/-- The actual prior/product-mark append integral is the raw likelihood
append action tested against the data observable. -/
theorem highAppendLikelihoodAction_prior_observable [MeasurableSpace E]
    [StandardBorelSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (dependent : 𝔐) (hsymm : 𝔇)
    (ν : Measure 𝔒) [IsProbabilityMeasure ν]
    (activation : 𝔞) (ham : Measurable activation)
    (Ba : ℝ) (hBa : 𝙑) (habound : ∀ e, |activation e| ≤ Ba)
    (n : ℕ) (a V P B : ℝ) (hP : 𝚏) (hB : 𝙐) (ha : 𝙞)
    (p F : 𝔊)
    (hp : 𝔟) (hF : 𝔠)
    (hpb : ∀ ω x, |𝗃₁| ≤ P) (hq : 𝔉)
    H (hH : Measurable H) (hHb : ∀ z, |H z| ≤ B)
    j :
     ∫ z : 𝔒 × E, 𝔍 ∂ν.prod π =
      ∫ z : 𝔣,
        𝔚 *
          𝔎
            ∂ν.prod 𝔏 := by
  have hg := (𝔥 highRawObservable_measurable p F hp hF H hH).comp
    𝔡
  have hi : Integrable (fun z => 𝔍) $ ν.prod π := by
    apply Integrable.of_bound (hg.mul $ ham.comp measurable_snd ).aestronglyMeasurable
      $ 𝔤 * (𝔏).real univ * Ba
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply, Function.comp_apply, abs_mul]
      exact mul_le_mul (𝔥 highRawObservable_abs_le P B hP hB _ _ (hpb _) ha (hq _) H hHb)
        (habound _) (abs_nonneg _) 𝖠₃
  have hi' : Integrable (fun z =>
      𝔚 *
        𝔎)
      $ ν.prod 𝔏 := by
    apply Integrable.of_bound
      (𝔔
        𝙾₂).aestronglyMeasurable
      $ B * 𝔖
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Pi.mul_apply, Function.comp_apply, Function.comp_apply, abs_mul]
      exact 𝘣 (highAppendLikelihoodAction_abs_le π dependent hsymm activation Ba hBa
        habound n a V P hP ha p F hpb hq j z.1 z.2) (abs_nonneg _) hB
  rw [MeasureTheory.integral_prod _ hi, MeasureTheory.integral_prod _ hi']
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    have he := highAppendLikelihoodAction_observable π dependent hsymm activation ham Ba hBa
      habound n a V P B hP hB ha p F hp hF hpb hq H hH hHb j ω
    grind
