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

def highWindowHolderConstant {d : ℕ} (C : ModelConstants d) : ℝ :=
  (2 : ℝ) ^ d * (((d + C.order).choose d : ℝ) + 2)

theorem highWindowHolderConstant_pos {d : ℕ} (C : ModelConstants d) :
    0 < highWindowHolderConstant C := by
  unfold highWindowHolderConstant
  positivity

/-- With the original binomial count, the full norm constant is exactly
the manuscript's C_w. -/
theorem highFrameField_original_model_bounds {d : ℕ} (C : ModelConstants d) :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k →
      ∀ cf : ℝ, 0 ≤ cf → ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) →
      let F := highFrameField d k (cf * (k : ℝ) ^ (-C.smoothness)) P
      (∀ x, |F x| ≤ (2 : ℝ) ^ d * (cf * (k : ℝ) ^ (-C.smoothness))) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) ≤ C.order → ∀ x,
        |multiPartial F (fun r => (γ r).val) x| ≤ (2 : ℝ) ^ d * cf) ∧
      (∀ γ : Fin d → Fin (C.order + 1), (∑ r, (γ r).val) = C.order → ∀ x y,
        |multiPartial F (fun r => (γ r).val) x - multiPartial F (fun r => (γ r).val) y| ≤
          (2 * ((2 : ℝ) ^ d * cf)) * euclideanNorm (x - y) ^ C.alpha) ∧
      (∀ U : Set (Covariate d), holderNorm U F C.order C.alpha ≤
        ENNReal.ofReal (highWindowHolderConstant C * cf)) := by
  obtain ⟨Cfr, hCfr, hbound⟩ := highFrameField_model_bounds C
  refine ⟨Cfr, hCfr, ?_⟩
  intro k hk0 hk cf hcf P hP
  letI := hk0
  obtain ⟨hv, hs, hm, _⟩ := hbound k hk0 hk cf hcf P hP
  refine ⟨hv, hs, hm, ?_⟩
  intro U
  have hh := holderNorm_of_global_mixed_bounds_binomial U _ C.order C.alpha
    ((2 : ℝ) ^ d * cf) (2 * ((2 : ℝ) ^ d * cf)) (by positivity) (by positivity) hs hm
  convert hh using 1
  congr 1
  unfold highWindowHolderConstant
  ring

theorem highFrame_ternary_amplitude_guards {d : ℕ} {C : ModelConstants d}
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 ≤ η → η ≤ η0 →
      η ^ 2 ≤ Q.ρ ∧ (2 : ℝ) ^ d * η ≤ Q.ρ / 2 := by
  let η0 := min (Real.sqrt Q.ρ) (Q.ρ / (2 * (2 : ℝ) ^ d))
  have hη0 : 0 < η0 := by
    dsimp [η0]
    exact lt_min (Real.sqrt_pos.2 Q.ρ_pos) (div_pos Q.ρ_pos (by positivity))
  refine ⟨η0, hη0, ?_⟩
  intro η hη hηU
  have hηsqrt : η ≤ Real.sqrt Q.ρ := hηU.trans (min_le_left _ _)
  have hηρ : η ≤ Q.ρ / (2 * (2 : ℝ) ^ d) := hηU.trans (min_le_right _ _)
  constructor
  · nlinarith [Real.sq_sqrt Q.ρ_pos.le, Real.sqrt_nonneg Q.ρ]
  · have h := (le_div_iff₀ (by positivity : 0 < 2 * (2 : ℝ) ^ d)).mp hηρ
    nlinarith

end NearlyMinimax
