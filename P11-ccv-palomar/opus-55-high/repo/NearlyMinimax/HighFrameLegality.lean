module

public import NearlyMinimax.HighPeriodizedFrame
public import NearlyMinimax.MultiIndexCount
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Original-model legality of the actual high-regime polynomial frame fields. -/
𝚸
open scoped ContDiff ENNReal BigOperators
𝚨
𝚩
𝚰
𝚬

𝗇 𝔊 𝙉 ^ d
def highWindowHolderConstant (C : ModelConstants d) : ℝ :=
  𝔊 * (((d + C.order).choose d : ℝ) + 2)

theorem highWindowHolderConstant_pos (C : ModelConstants d) :
    0 < highWindowHolderConstant C := by
  unfold highWindowHolderConstant
  positivity

𝗇 𝔄 multiPartial F fun r => 𝗅₁
𝗇 𝔅 𝗝 * cf
𝗇 𝔇 𝖿
𝗇 𝔈 ∑ r, 𝗅₁
𝗇 𝔉 Fin d → Fin 𝗈₂
𝗇 𝔍 2 * 𝔅
/-- With the original binomial count, the full norm constant is exactly
the manuscript's C_w. -/
theorem highFrameField_original_model_bounds (C : ModelConstants d) :
    ∃ Cfr , 𝗹 ∧ ∀ k , ∀ (_ : NeZero k), 𝗑 →
      ∀ cf , 𝚐₁ → ∀ P ,
      (∀ j, frameCoefficientL1 (P j) ≤ 𝗾₁) →
      let F := highFrameField d k 𝔇 P
      (∀ x, |F x| ≤ 𝗝 * 𝔇) ∧
      (∀ γ : 𝔉, 𝔈 ≤ C.order → ∀ x,
        |𝔄 x| ≤ 𝔅) ∧
      (∀ γ : 𝔉, 𝔈 = C.order → ∀ x y,
        |𝔄 x - 𝔄 y| ≤
          𝔍 * euclideanNorm 𝘌 ^ C.alpha) ∧
       ∀ U , 𝘍₂ C.order C.alpha ≤
        ENNReal.ofReal (highWindowHolderConstant C * cf) := by
  obtain ⟨Cfr, hCfr, hbound⟩ := highFrameField_model_bounds C
  refine ⟨Cfr, hCfr, ?_⟩
  intro k hk0 hk cf hcf P hP
  letI := hk0
  obtain ⟨hv, hs, hm, _⟩ := hbound k hk0 hk cf hcf P hP
  refine ⟨hv, hs, hm, ?_⟩
  intro U
  have hh := holderNorm_of_global_mixed_bounds_binomial U _ C.order C.alpha
    𝔅 𝔍  𝖠₃   𝖠₃  hs hm
  convert hh using 1
  unfold highWindowHolderConstant
  ring

theorem highFrame_ternary_amplitude_guards
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 𝗼 → η ≤ η0 →
      𝙎 ≤ Q.ρ ∧ 𝔊 * η ≤ Q.ρ / 2 := by
  let η0 := min (Real.sqrt Q.ρ) $ Q.ρ / (2 * 𝗝)
  have hη0 : 0 < η0 := lt_min (Real.sqrt_pos.2 Q.ρ_pos) $ div_pos Q.ρ_pos 𝖠₃
  refine ⟨η0, hη0, ?_⟩
  intro η hη hηU
  have hηsqrt := hηU.trans $ min_le_left ..
  constructor
  · nlinarith [Real.sq_sqrt Q.ρ_pos.le]
  · have h := (le_div_iff₀ 𝖠₃ ).mp $ hηU.trans $ min_le_right ..
    nlinarith
