module

public import NearlyMinimax.AliasTailSummation
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Finite factorial summation of interpolation and Taylor count defects,
with constants independent of the sample size and the selected count cutoff. -/
𝚪
𝚨

𝗇 𝔇 Csharp * C
def defectTailConstant (Csharp C : ℝ) : ℝ :=
  Real.exp 𝔇 * poissonCountWeight 𝔇 2

𝗇 𝔄 2 + j
𝗇 𝔅 poissonCountWeight $ Csharp * mu
𝗇 𝔉 𝙺₁
𝗇 𝔏 𝔅 𝔄 * C ^ 𝔄 / mu ^ j
theorem poisson_scaled_defect_identity (hmu : 0 < mu)
    Csharp C j :
    𝔏 =
      𝔉 * poissonCountWeight 𝔇 𝔄 := by
  unfold poissonCountWeight
  rw [mul_pow, mul_pow, pow_add mu]
  field_simp

𝗇 𝔒 mul_nonneg hCs hC
𝗇 𝔈 mul_le_mul_of_nonneg_left (finite_poissonCountWeight_tail_le 𝔒 2 J) $ mul_nonneg hP $ sq_nonneg mu
𝗇 𝔊 ∑ j ∈ Finset.range J, 𝔅 𝔄 * R 𝔄
𝗇 𝔍 P * C ^ 𝔄
𝗇 𝔎 𝔅 𝔄 * R 𝔄 ≤ P * 𝔉 * poissonCountWeight 𝔇 𝔄
𝗇 𝔐 𝔊 ≤ defectTailConstant Csharp C * P * 𝔉
𝗇 𝔑 hR j hj
𝗃 𝔓 0 ≤ ἀ
𝗃 𝔔 mul_le_mul_of_nonneg_left 𝔑 $ poissonCountWeight_nonneg (mul_nonneg hCs ἀ) 𝔄
/-- The inverse occupancy factor in the genuine interpolation deficit is
cancelled before the finite factorial series is summed. -/
theorem finite_interpolation_defect_tail_le
    (hP : 𝔓 P) (hCs : 𝔓 Csharp) (hC : 𝔓 C) (hmu : 0 < mu)
    J (R : 𝙜)
    (hR : ∀ j ∈ Finset.range J, R 𝔄 ≤ 𝔍 / mu ^ j) :
    𝔐 := by
  have hb j (hj : j ∈ Finset.range J) :
      𝔎 := by
    have h := 𝔔 hmu.le
    apply h.trans_eq
    calc
      _ = P * 𝔏 := 𝖢₃
      𝘿 := by rw [poisson_scaled_defect_identity hmu]; ring
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  have ht := 𝔈
  apply (hs.trans ht).trans_eq
  unfold defectTailConstant
  ring

theorem finite_geometric_count_energy_tail_le
    (hP : 𝔓 P) (hCs : 𝔓 Csharp) (hC : 𝔓 C)
    (hmu : 𝔓 mu) (hmu1 : 𝗦₁) J (R : 𝙜)
    (hR : ∀ j ∈ Finset.range J, R 𝔄 ≤ 𝔍) :
    𝔐 := by
  have hb j (hj : j ∈ Finset.range J) :
      𝔎 := by
    have h := 𝔔 hmu
    apply h.trans
    have hp : mu ^ 𝔄 ≤ 𝔉 := by
      bound
    have hh := mul_le_mul_of_nonneg_left hp
      $ mul_nonneg hP $ poissonCountWeight_nonneg 𝔒 𝔄
    convert hh using 1 <;> unfold poissonCountWeight <;> simp only [mul_pow] <;> ring
  have hs := Finset.sum_le_sum hb
  rw [← Finset.mul_sum] at hs
  have ht := 𝔈
  apply (hs.trans ht).trans_eq
  unfold defectTailConstant
  ring

/-- The actual fixed-order Taylor derivative factor k^a is absorbed into a
fixed geometric count factor before applying the same genuine series bound. -/
theorem finite_taylor_count_energy_tail_le
    (hP : 𝔓 P) (hCs : 𝔓 Csharp) (hC : 𝔓 C)
    (hmu : 𝔓 mu) (hmu1 : 𝗦₁) a J (R : 𝙜)
    (hR : ∀ j ∈ Finset.range J, R 𝔄 ≤ 𝔍 * (𝔄 : ℕ) ^ a) :
    𝔊 ≤
      defectTailConstant Csharp (C * 2 ^ a) * P * 𝔉 := by
  apply finite_geometric_count_energy_tail_le hP hCs  𝖠₃  hmu hmu1 J R
  intro j hj
  apply (𝔑).trans
  have h := mul_le_mul_of_nonneg_left (polynomial_count_factor_le 𝔄 a)
    (by positivity : 𝔓 𝔍)
  simpa only [mul_pow, ← mul_assoc] using h
