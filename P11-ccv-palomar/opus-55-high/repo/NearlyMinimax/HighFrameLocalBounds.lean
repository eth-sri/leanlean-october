module

public import NearlyMinimax.HighLocalFrame
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗍

/-! Actual coordinatewise chart bounds for the finite polynomial frame. -/
𝚪
𝚨
𝚩
𝚱

theorem highFrameFeature_abs_le_one x
    (hx : ∀ i, |x i| ≤ 2) (γ : HighFrameIndex d F) :
    |highFrameFeature x γ| ≤ 1 := by
  unfold highFrameFeature
  rw [Finset.abs_prod]
  apply Finset.prod_le_one₀
  · simp
  · intro i _
    rw [abs_pow]
    have hb : |x i / 8| ≤ 1 := by
      grind
    bound

𝗇 𝔄 𝖲
𝗇 𝔅 ∑ γ, highFrameFeature x γ * v γ
theorem highFrameProfile_abs_le_coefficients x
    (hx : ∀ i, |x i| ≤ 2) (v : 𝔄) :
    |𝔅| ≤ ∑ γ, |v γ| := by
  apply 𝘡
  apply Finset.sum_le_sum
  intro γ _
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (highFrameFeature_abs_le_one x hx γ) $ abs_nonneg _ ).trans_eq $ one_mul _

theorem highFrameProfile_abs_le_one C (hC : 1 ≤ C)
    x (hx : ∀ i, |x i| ≤ 2) (v : 𝔄)
    (hv : ∑ γ, |v γ| ≤ 𝗳) :
    |𝔅| ≤ 1 :=
  (highFrameProfile_abs_le_coefficients x hx v).trans $ hv.trans $ inv_le_one_of_one_le₀ hC

theorem highFrameCoefficientRegression_abs_le
    C η ρ (hC : 1 ≤ C) (hη : 𝗼) (hηρ : η ≤ 𝙸)
    (U : 𝙇) (hU : ∀ i l, |𝚅| ≤ 2)
    g w (hg : ∀ i, |g i| ≤ 𝙸) (hw : ∀ i, |w i| ≤ 1)
    (c : 𝔄) (hc : ∑ γ, |c γ| ≤ 𝗳) i :
    |𝗡 𝙬 c i| ≤ ρ := by
  have hwη : |𝗌₂| ≤ η := by
    rw [abs_mul, abs_of_nonneg hη]
    bound
  have hterm : |𝗌₂*(∑ γ, highFrameFeature (U i) γ * c γ)| ≤ η := by
    rw [abs_mul]
    exact (mul_le_mul hwη (highFrameProfile_abs_le_one C hC (U i) (hU i) c hc) (abs_nonneg _) hη).trans_eq $ mul_one _
  unfold coefficientRegression
  grind
