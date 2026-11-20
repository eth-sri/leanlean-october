module

public import NearlyMinimax.HighPeriodizedFrame
public import NearlyMinimax.MultiIndexCount

@[expose] public section

/-! Original-model legality of the actual high-regime polynomial frame fields. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local instance] Classical.propDecidable

variable {d : ℕ} (C : ModelConstants d)

def highWindowHolderConstant : ℝ :=
  2 ^ d * (((d + C.order).choose d) + 2)

theorem highWindowHolderConstant_pos :
    0 < highWindowHolderConstant C := by
  unfold highWindowHolderConstant
  positivity

/-- With the original binomial count, the full norm constant is exactly
the manuscript's C_w. -/
theorem highFrameField_original_model_bounds :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k, ∀ (_ : NeZero k), 4 ≤ k →
      ∀ cf, 0 ≤ cf → ∀ P,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) →
      let F := highFrameField k (cf * k ^ (-C.smoothness)) P
      (∀ x, |F x| ≤ 2 ^ d * (cf * k ^ (-C.smoothness))) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
        |multiPartial F (fun r => (γ r).val) x| ≤ 2 ^ d * cf) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
        |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
          (2 * (2 ^ d * cf)) * euclideanNorm (x - y) ^ C.alpha) ∧
      (∀ U, holderNorm U F C.order C.alpha ≤
        ENNReal.ofReal (highWindowHolderConstant C * cf)) := by
  obtain ⟨Cfr, hCfr, hbound⟩ := highFrameField_model_bounds C
  refine ⟨Cfr, hCfr, ?_⟩
  intro k hk0 hk cf hcf P hP
  letI := hk0
  obtain ⟨hv, hs, hm, _⟩ := hbound k hk0 hk cf hcf P hP
  refine ⟨hv, hs, hm, ?_⟩
  intro U
  have hh := holderNorm_of_global_mixed_bounds U (by positivity) (by positivity) (bounded_multiIndex_count_le _ _) hs hm
  convert hh using 1
  congr 1
  unfold highWindowHolderConstant
  ring

theorem highFrame_ternary_amplitude_guards {C : ModelConstants d}
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η, 0 ≤ η → η ≤ η0 →
      η ^ 2 ≤ Q.ρ ∧ 2 ^ d * η ≤ Q.ρ / 2 := by
  let η0 := min (Real.sqrt Q.ρ) (Q.ρ / (2 * 2 ^ d))
  have hη0 : 0 < η0 := by
    exact lt_min (Real.sqrt_pos.2 Q.ρ_pos) (div_pos Q.ρ_pos (by positivity))
  refine ⟨η0, hη0, ?_⟩
  intro η hη hηU
  have hηsqrt  := hηU.trans (min_le_left _ _)
  have hηρ  := hηU.trans (min_le_right _ _)
  constructor
  · nlinarith [Real.sq_sqrt Q.ρ_pos.le, Real.sqrt_nonneg Q.ρ]
  · have h := (le_div_iff₀ (by positivity)).mp hηρ
    nlinarith

end NearlyMinimax
