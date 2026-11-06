module

public import NearlyMinimax.HighLikelihoodDerivative
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual raw data observables and the mass-tilted original observation mean. -/
𝚹
𝛉
𝚨
𝚭
𝚩
𝛂

𝗇 𝔄 𝙀
𝗇 𝔍 𝘱
𝗃 𝔓 ἀ n a V
𝗃 𝔏 𝔓 ἀ p F
𝗇 𝔐 𝙌 → ℝ
𝗇 𝔒 𝗟₁
𝗃 𝔖 ∫ z, H 𝔒 * 𝔏 ἀ z ∂𝔍
def highRawObservable (n : ℕ) (a V : ℝ) (p F : 𝔄)
    (H : 𝔐) : ℝ :=
  𝔖 highRawSampleLikelihood

def highRawObservableVarianceDerivative (n : ℕ) (a V : ℝ) (p F : 𝔄)
    (H : 𝔐) : ℝ :=
  𝔖 highRawSampleVarianceDerivative

𝗇 𝔇 (hH.comp $ encodeDesignResponse_measurable a ).comp measurable_snd
𝗇 𝔊 𝔓 highRawObservable (p ω) (F ω) H
𝗃 𝔔 𝔏 ἀ hp hF
𝗇 𝔎 𝔔 highRawSampleLikelihood_joint_measurable
𝗃 𝔗 Measurable $ Function.uncurry ἀ
theorem highRawObservable_measurable n a V
    (p F : Ω → 𝔄) (hp : 𝔗 p)
    (hF : 𝔗 F) H
    (hH : Measurable H) : Measurable fun ω => 𝔊 := by
  have h :=
    (𝔇).mul
      𝔎
  exact h.stronglyMeasurable.integral_prod_right'.measurable

theorem highRawObservableVarianceDerivative_measurable n a V
    (p F : Ω → 𝔄) (hp : 𝔗 p)
    (hF : 𝔗 F) H
    (hH : Measurable H) :
    Measurable fun ω => 𝔓 highRawObservableVarianceDerivative (p ω) (F ω) H := by
  have h :=
    (𝔇).mul
      𝔔 highRawSampleVarianceDerivative_joint_measurable
  exact h.stronglyMeasurable.integral_prod_right'.measurable

𝗇 𝔉 𝗨
theorem highRawObservable_abs_le n a V P B (hP : 𝚏) (hB : 𝙐)
    (p F : 𝔄) (hp : ∀ x, |p x| ≤ P) (ha : 𝙞)
    (hq : 𝔉)
    H (hHb : ∀ z, |H z| ≤ B) :
    |𝔏 highRawObservable H| ≤ B * 𝚗 * (𝔍).real Set.univ := by
  rw [highRawObservable, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    exact 𝘣 (𝔓 highRawSampleLikelihood_abs_le P hP p F hp ha hq z)
      (abs_nonneg _) hB

theorem highRawObservableVarianceDerivative_abs_le n a V P B
    (ha : 𝙆) (hP : 𝚏) (hB : 𝙐)
    (p F : 𝔄) (hp : ∀ x, |p x| ≤ P)
    (hq : 𝔉)
    H (hHb : ∀ z, |H z| ≤ B) :
    |𝔏 highRawObservableVarianceDerivative H| ≤
      B * (𝚗 * (n / 𝗅)) * (𝔍).real Set.univ := by
  rw [highRawObservableVarianceDerivative, ← Real.norm_eq_abs]
  apply norm_integral_le_of_norm_le_const
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_mul]
    exact 𝘣 (𝔓 highRawSampleVarianceDerivative_abs_le P ha hP p F hp hq z)
      (abs_nonneg _) hB

𝗇 𝔅 𝙙
𝗇 𝔈 𝙽₂
𝗇 𝔑 fun z => 𝔈
/-- The actual original real-data mean under the genuine mass tilt equals
G_n^-1 times the raw-likelihood observable mean. -/
theorem massPowerTilt_highReal_observable_mean (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (a V : ℝ) (p F : Ω → 𝔄)
    hp hF
    aRaw bRaw (haRaw : 𝙓)
    (hraw : 𝙄) (ha : 𝙞)
    (hq : ∀ ω x y, 0 ≤ 𝙅 V y)
    H (hH : Measurable H)
    B (hB : 𝙐) (hHb : ∀ z, |H z| ≤ B) :
     ∫ ω, ∫ z, H z ∂𝔔 highRealSampleKernel ω
      ∂massPowerTilt ν 𝔅 n =
      (massPowerNormalizer ν 𝔅 n)⁻¹ *
        ∫ ω, 𝔊 ∂ν := by
  let m := 𝔅
  have hm := 𝙨
  have hbound ω :=
    𝙕
  let _ := massPowerTilt_isProbability ν m hm n aRaw bRaw haRaw hbound
  let _ := 𝔔 highSampleIndexKernel_markov aRaw bRaw haRaw hraw ha hq
  have hM : Measurable fun z : Ω × 𝙇 × 𝙈 =>
      𝔈 := 𝔇
  have hInt : Integrable 𝔑
      $ (massPowerTilt ν m n).compProd 𝔔 highSampleIndexKernel := by
    apply Integrable.of_bound hM.aestronglyMeasurable B
    simp_all
  have hpabs ω x : |𝗃₁| ≤ |bRaw| := by
    grind
  have hIntRaw : Integrable (fun z =>
      𝔓 highRawSampleLikelihood (p z.1) (F z.1) z.2 * 𝔈)
      $ ν.prod 𝔍 := by
    apply Integrable.of_bound ((𝔎).mul hM).aestronglyMeasurable
      $ |bRaw| ^ n * B
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
      exact mul_le_mul (𝔓 highRawSampleLikelihood_abs_le |bRaw| (abs_nonneg _) (p z.1) (F z.1)
        (hpabs z.1) ha (hq z.1) z.2) (hHb _) (abs_nonneg _) $ pow_nonneg (abs_nonneg _) n
  have he := massPowerTilt_highSample_integral ν n a V p F hp hF aRaw bRaw haRaw hraw hq
    𝔑
  rw [Measure.integral_compProd hInt, MeasureTheory.integral_prod _ hIntRaw] at he
  convert he using 1
  · apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      dsimp
      rw [highRealSampleKernel_apply,
        integral_map_of_stronglyMeasurable (encodeDesignResponse_measurable a) hH.stronglyMeasurable]
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      dsimp only [highRawObservable]
      grind
