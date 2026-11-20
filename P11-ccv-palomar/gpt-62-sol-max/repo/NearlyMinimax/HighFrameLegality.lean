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

section
variable {d : ℕ}

theorem highWindowHolderConstant_pos (C : ModelConstants d) :
    0 < highWindowHolderConstant C := by
  unfold highWindowHolderConstant
  positivity

/-- With the original binomial count, the full norm constant is exactly
the manuscript's C_w. -/
theorem highFrameField_original_model_bounds (C : ModelConstants d) :
    ∃ Cfr : ℝ, 1 ≤ Cfr ∧ ∀ k : ℕ, ∀ (_ : NeZero k), 4 ≤ k →
      ∀ cf : ℝ, 0 ≤ cf → ∀ P : HighWindowLabels d k → MvPolynomial (Fin d) ℝ,
      (∀ j, frameCoefficientL1 (P j) ≤ Cfr⁻¹) →
      let F := highFrameField d k (cf * (k : ℝ) ^ (-C.smoothness)) P
      (∀ x, |F x| ≤ (2 : ℝ) ^ d * (cf * (k : ℝ) ^ (-C.smoothness))) ∧
      (∀ U : Set (Covariate d), holderNorm U F C.order C.alpha ≤
        ENNReal.ofReal (highWindowHolderConstant C * cf)) := by
  obtain ⟨Cfr, hCfr1, hCfr⟩ := highFrameField_derivative_bound d (C.order + 1)
  refine ⟨Cfr, hCfr1, ?_⟩
  intro k hk0 hk cf hcf P hP
  letI := hk0
  let η := cf * (k : ℝ) ^ (-C.smoothness)
  let F := highFrameField d k η P
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (by omega : 1 ≤ k)
  have hkpos : (0 : ℝ) < k := zero_lt_one.trans_le hkR
  have hη : 0 ≤ η := by positivity
  have hbound (q : ℕ) (hq : q ≤ C.order + 1) x :
      ‖iteratedFDeriv ℝ q F x‖ ≤ ((2 : ℝ) ^ d * cf) * (k : ℝ) ^ ((q : ℝ) - C.smoothness) := by
    have hh := hCfr k hk0 hk η P hP q hq x
    rw [abs_of_nonneg hη] at hh
    convert hh using 1
    dsimp [η]
    rw [show (q : ℝ) - C.smoothness = -C.smoothness + q by ring, Real.rpow_add hkpos, Real.rpow_natCast]
    ring
  obtain ⟨hs, hm⟩ := mixed_bounds_of_scaled_derivatives C F
    (highFrameField_contDiff _ _ _ _) (k : ℝ) ((2 : ℝ) ^ d * cf) hkR (by positivity) hbound
  refine ⟨fun x => ?_, fun U => ?_⟩
  · simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.cast_zero, zero_sub, mul_assoc]
      using hbound 0 (by omega) x
  · convert holderNorm_of_global_mixed_bounds_of_count U F C.order C.alpha
      ((2 : ℝ)^d * cf) (2 * ((2 : ℝ)^d * cf)) (by positivity) (by positivity)
      _ (bounded_multiIndex_count_le d C.order) hs hm using 2
    unfold highWindowHolderConstant
    ring

theorem highFrame_ternary_amplitude_guards {C : ModelConstants d}
    (Q : LowSmoothnessTernaryConstants C) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 ≤ η → η ≤ η0 →
      η ^ 2 ≤ Q.ρ ∧ (2 : ℝ) ^ d * η ≤ Q.ρ / 2 := by
  let η0 := min (Real.sqrt Q.ρ) (Q.ρ / (2 * (2 : ℝ) ^ d))
  have hη0 : 0 < η0 := lt_min (Real.sqrt_pos.2 Q.ρ_pos) (div_pos Q.ρ_pos (by positivity))
  refine ⟨η0, hη0, ?_⟩
  intro η hη hηU
  have hηsqrt := hηU.trans (min_le_left _ _)
  have hηρ := hηU.trans (min_le_right _ _)
  constructor
  · nlinarith [Real.sq_sqrt Q.ρ_pos.le, Real.sqrt_nonneg Q.ρ]
  · have h := (le_div_iff₀ (by positivity : 0 < 2 * (2 : ℝ) ^ d)).mp hηρ
    nlinarith

end

end NearlyMinimax
