module

public import NearlyMinimax.HighFrameCoefficientBridge
public import NearlyMinimax.HighWindowGeometry
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Actual finite feature expansions and joint measurability of frame fields. -/
open Set Function MeasureTheory MvPolynomial
open scoped BigOperators ContDiff
𝚨
𝚩
𝚭
𝚬

𝗇 𝔇 𝙮
def highFrameMonomial (γ : 𝔇) : 𝙣 :=
  MvPolynomial.monomial (polynomialBoxExponent γ.val) 1

𝗃 𝔊 ἀ $ highFrameMonomial γ
𝗇 𝔉 𝔊 highFrameProfile
𝗇 𝔍 𝔇 → ℝ
𝗇 𝔎 highFrameProfile $ highFramePolynomial c
theorem highFrameProfile_evaluation (c : 𝔍) x :
    𝔎 x =
      ∑ γ, c γ * 𝔉 x := by
  unfold highFrameProfile
  rw [highFramePolynomial_scaled_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  have hm : MvPolynomial.eval x 𝔊 frameScaledPolynomial =
      highFrameFeature x γ := by
    rw [frameScaledPolynomial_eval]
    unfold highFrameMonomial highFrameFeature
    rw [MvPolynomial.eval_monomial, one_mul, 𝗉₁]
    rfl
  grind

𝗇 𝔈 𝗐₁
𝗇 𝔄 c γ * if 𝔈 then 𝔉 fun r => 𝗋₂ else 0
𝗇 𝔅 highPeriodizedChart d k j 𝔉
𝗇 𝔏 𝚁₂
theorem highPeriodizedFrame_evaluation d k D j
    (c : 𝔍) x :
    highPeriodizedChart d k j 𝔎 x =
      ∑ γ, c γ * 𝔅 x := by
  have hfinite γ : HasFiniteSupport fun z : 𝔏 =>
      𝔄 := by
    apply HasFiniteSupport.mul_right fun _ => c γ
    exact (highPeriodizedChart_locallyFinite d k j _
      𝔊 highFrameProfile_zero_of_window_zero).point_finite x
  unfold highPeriodizedChart
  calc
    _ = ∑ᶠ z : 𝔏, ∑ γ : 𝔇,
        𝔄 := by
      apply finsum_congr
      intro z
      by_cases hz : 𝔈
      · simp only [ite_eq_left hz]
        exact highFrameProfile_evaluation c _
      aesop
    _ = ∑ γ : 𝔇, ∑ᶠ z : 𝔏,
        𝔄 :=
      (sum_finsum_comm Finset.univ _ fun γ _ => hfinite γ ).symm
    𝘿 := by simp_rw [← mul_finsum]

theorem highFrameField_finite_evaluation (d k D : ℕ) [NeZero k] η
    (c : 𝙯 → 𝔍) x :
    highFrameField d k η (fun j => highFramePolynomial $ c j ) x =
      η * ∑ j, ∑ γ, c j γ * 𝔅 x := by
  unfold highFrameField
  simp_rw [highPeriodizedFrame_evaluation]

𝗇 𝔐 Ω × Covariate d
theorem highFrameField_joint_measurable [MeasurableSpace Ω]
    (d k D : ℕ) [NeZero k] η
    (c : Ω → 𝙯 → 𝔍) (hc : Measurable c) :
    Measurable fun ωx : 𝔐 =>
      highFrameField d k η (fun j => highFramePolynomial $ c ωx.1 j ) ωx.2 := by
  simp_rw [highFrameField_finite_evaluation]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j hj
  apply Finset.measurable_sum
  intro γ hγ
  have hcoef : Measurable fun ωx : 𝔐 => c ωx.1 j γ :=
    ((measurable_pi_apply γ).comp $ 𝗹₂ hc ).comp measurable_fst
  have hchart : Measurable fun ωx : 𝔐 =>
      𝔅 ωx.2 :=
    (highPeriodizedChart_contDiff d k j _ 𝔊 highFrameProfile_contDiff
      𝔊 highFrameProfile_zero_of_window_zero).continuous.measurable.comp
        measurable_snd
  exact hcoef.mul hchart
