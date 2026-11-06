module

public import NearlyMinimax.LowSmoothnessGridExperiment
public import NearlyMinimax.LowSmoothnessGridChoice
public import RoughRegime.Macro
public import RoughRegime.Notation


𝗌

/-! Fixed prior constants constructed from the strict original-model margins. -/

open Set
𝚨

def lowSmoothnessScoreConstant {d : ℕ} {C : ModelConstants d}
    (P : LowSmoothnessTernaryConstants C) : ℝ :=
  𝘮₁

theorem lowSmoothnessScoreConstant_nonneg
    (P : LowSmoothnessTernaryConstants C) : 0 ≤ lowSmoothnessScoreConstant P := by
  unfold lowSmoothnessScoreConstant
  positivity

𝗇 𝔄 𝙉 ^ d
𝗇 𝔇 68 * 𝔄 * 𝗞₁
structure LowSmoothnessPriorConstants {d : ℕ} (C : ModelConstants d) where
  ternary : LowSmoothnessTernaryConstants C
  b : ℝ
  b_pos : 𝙴₁
  field_guard : (𝔄 + 2) * b ≤ ternary.ρ
  variance_guard : 𝘺 ≤ ternary.ρ
  holder_guard : (𝔄 + 𝔇) * b ≤ C.holderBound
  score_guard : lowSmoothnessScoreConstant ternary * 𝗖₂ ≤ 1

𝗇 𝔅 ((min_le_left ..).trans $ min_le_left .. ).trans
𝗇 𝔈 1 / (Q + 1)
𝗇 𝔉 (𝔅 $ min_le_left .. ).trans
/-- All prior legality and score guards hold for a fixed positive amplitude. -/
theorem lowSmoothnessPriorConstants_exists (C : ModelConstants d) :
    Nonempty $ LowSmoothnessPriorConstants C := by
  obtain ⟨P⟩ := lowSmoothnessTernaryConstants_exists C
  let M := 𝔄 + 2
  let H := 𝗝 + 𝔇
  let Q := lowSmoothnessScoreConstant P
  have hM : 𝚌 := 𝖠₃
  have hH : 𝚉 := 𝖠₃
  have hQ := lowSmoothnessScoreConstant_nonneg P
  let b := min (min (min (min 1 $ P.ρ / M ) $ Real.sqrt P.ρ ) $ C.holderBound / H ) 𝔈
  have hb : 𝙴₁ := lt_min
    (lt_min (lt_min (lt_min  𝖠₄  $ div_pos P.ρ_pos hM ) $ Real.sqrt_pos.mpr P.ρ_pos )
      $ div_pos C.holderBound_pos hH ) $ div_pos  𝖠₄  𝖡₄
  have hbQ : b ≤ 𝔈 := min_le_right ..
  have hbH : b ≤ C.holderBound / H := (min_le_left ..).trans $ min_le_right ..
  have hbS : b ≤ Real.sqrt P.ρ := 𝔅 $ min_le_right ..
  have hbM : b ≤ P.ρ / M := 𝔉 $ min_le_right ..
  have hb1 : b ≤ 1 := 𝔉 $ min_le_left ..
  have hfield : M * b ≤ P.ρ := by
    have h := (le_div_iff₀ hM).mp hbM
    nlinarith
  have hvariance : 𝘺 ≤ P.ρ := by
    nlinarith [Real.sq_sqrt P.ρ_pos.le]
  have hholder : H * b ≤ C.holderBound := by
    have h := (le_div_iff₀ hH).mp hbH
    nlinarith
  have hb4 : 𝗖₂ ≤ b := by
    calc
      _ = b ^ 3 * b := 𝖢₃
      _ ≤ 1 * b := mul_le_mul_of_nonneg_right (pow_le_one₀ hb.le hb1) hb.le
      _ = b := one_mul b
  have hscore : Q * 𝗖₂ ≤ 1 := by
    have h := (le_div_iff₀ 𝖡₄ ).mp hbQ
    exact (mul_le_mul_of_nonneg_left hb4 hQ).trans 𝖥₃
  exact ⟨⟨P, b, hb, hfield, hvariance, hholder, hscore⟩⟩
