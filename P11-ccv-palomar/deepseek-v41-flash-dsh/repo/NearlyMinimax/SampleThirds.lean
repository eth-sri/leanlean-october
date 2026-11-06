module

public import NearlyMinimax.SampleRemainder


@[expose] public section

/-! Two pilots and one evaluation block from arbitrary original sample sizes. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax

def threeBlockSize (n : ℕ) : ℕ := n / 3

def threeBlockRemainder (n : ℕ) : ℕ := n - (threeBlockSize n + threeBlockSize n + threeBlockSize n)

variable (n : ℕ)

theorem threeBlockTotal :
    n = threeBlockSize n + threeBlockSize n + threeBlockSize n + threeBlockRemainder n := by
  simp only [threeBlockSize, threeBlockRemainder]
  omega

section
variable {n : ℕ}

theorem threeBlockSize_two_le (hn : 6 ≤ n) : 2 ≤ threeBlockSize n := by
  unfold threeBlockSize
  omega

theorem threeBlockSize_fraction (hn : 6 ≤ n) :
    (1 / 4 : ℝ) * n ≤ threeBlockSize n := by
  have h : n ≤ 4 * threeBlockSize n := by unfold threeBlockSize; omega
  have hR : (n : ℝ) ≤ 4 * (threeBlockSize n : ℝ) := by exact_mod_cast h
  linarith

end

section
variable {d n m : ℕ}

def castEstimator (h : n = m) (T : Estimator d m) : Estimator d n := h.symm ▸ T

theorem castEstimator_risk_eq (h : n = m) (T : Estimator d m)
    (θ : RegressionParameter d) : meanSquaredRisk (castEstimator h T) θ = meanSquaredRisk T θ := by
  subst m
  rfl

end

section
variable {d n : ℕ}

def threeBlockEstimator 
    (T : (((Fin (threeBlockSize n) → Observation d) × (Fin (threeBlockSize n) → Observation d)) ×
      (Fin (threeBlockSize n) → Observation d)) → ℝ) (hmT : Measurable T) : Estimator d n :=
  castEstimator (threeBlockTotal n)
    (blockEstimatorWithRemainder (r := threeBlockRemainder n) T hmT)

theorem threeBlockEstimator_risk_eq (C : ModelConstants d)
    (θ : RegressionParameter d) (hθ : Admissible C θ)
    (T : (((Fin (threeBlockSize n) → Observation d) × (Fin (threeBlockSize n) → Observation d)) ×
      (Fin (threeBlockSize n) → Observation d)) → ℝ) (hmT : Measurable T) :
    meanSquaredRisk (threeBlockEstimator T hmT) θ =
      ∫⁻ z, ENNReal.ofReal ((T z - θ.variance) ^ 2)
        ∂((sampleLaw θ (threeBlockSize n)).prod (sampleLaw θ (threeBlockSize n))).prod
          (sampleLaw θ (threeBlockSize n)) := by
  rw [threeBlockEstimator, castEstimator_risk_eq]
  exact blockEstimatorWithRemainder_risk_eq C θ hθ T hmT

end

end NearlyMinimax
