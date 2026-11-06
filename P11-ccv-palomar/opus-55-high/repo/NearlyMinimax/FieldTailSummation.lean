module

public import NearlyMinimax.DefectTailSummation
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! True finite factorial summation of the higher-field term, whose first
possible selected count is four. -/
𝚪
𝚨

𝗇 𝔅 Csharp * C
def fieldTailConstant (Csharp C : ℝ) : ℝ :=
  Real.exp 𝔅 * poissonCountWeight 𝔅 4

𝗇 𝔄 4 + j
𝗇 𝔇 Csharp * mu
𝗇 𝔈 ∑ j ∈ Finset.range J, poissonCountWeight 𝔇 𝔄 * R 𝔄
𝗇 𝔉 P * C ^ 𝔄
𝗇 𝔊 mu ^ 4
𝗇 𝔍 mul_nonneg hCs hC
𝗃 𝔎 0 ≤ ἀ
theorem finite_geometric_field_count_tail_le
    (hP : 𝔎 P) (hCs : 𝔎 Csharp) (hC : 𝔎 C)
    (hmu : 𝔎 mu) (hmu1 : 𝗦₁) J (R : 𝙜)
    (hR : ∀ j ∈ Finset.range J, R 𝔄 ≤ 𝔉) :
    𝔈 ≤
      fieldTailConstant Csharp C * P * 𝔊 := by
  have hb j (hj : j ∈ Finset.range J) :
      poissonCountWeight 𝔇 𝔄 * R 𝔄 ≤
      P * 𝔊 * poissonCountWeight 𝔅 𝔄 := by
    have h := mul_le_mul_of_nonneg_left (hR j hj)
      $ poissonCountWeight_nonneg (mul_nonneg hCs hmu) 𝔄
    apply h.trans
    have hp : mu ^ 𝔄 ≤ 𝔊 := by
      bound
    have hh := mul_le_mul_of_nonneg_left hp
      $ mul_nonneg hP $ poissonCountWeight_nonneg 𝔍 𝔄
    convert hh using 1 <;> unfold poissonCountWeight <;> simp only [mul_pow] <;> ring
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  have ht := mul_le_mul_of_nonneg_left
    (finite_poissonCountWeight_tail_le 𝔍 4 J)
    $ mul_nonneg hP $ pow_nonneg hmu 4
  apply (hs.trans ht).trans_eq
  unfold fieldTailConstant
  ring

theorem finite_polynomial_field_count_tail_le
    (hP : 𝔎 P) (hCs : 𝔎 Csharp) (hC : 𝔎 C)
    (hmu : 𝔎 mu) (hmu1 : 𝗦₁) a J (R : 𝙜)
    (hR : ∀ j ∈ Finset.range J, R 𝔄 ≤ 𝔉 * (𝔄 : ℕ) ^ a) :
    𝔈 ≤
      fieldTailConstant Csharp (C * 2 ^ a) * P * 𝔊 := by
  apply finite_geometric_field_count_tail_le hP hCs  𝖠₃  hmu hmu1 J R
  intro j hj
  apply (hR j hj).trans
  have h := mul_le_mul_of_nonneg_left (polynomial_count_factor_le 𝔄 a)
    (by positivity : 𝔎 𝔉)
  simpa only [mul_pow, ← mul_assoc] using h
