module

public import NearlyMinimax.SampleRemainder


@[expose] public section

/-! Two pilots and one evaluation block from arbitrary original sample sizes. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false

section
variable (n : ℕ)

def threeBlockSize : ℕ := n / 3

def threeBlockRemainder : ℕ := n - (threeBlockSize n + threeBlockSize n + threeBlockSize n)

theorem threeBlockTotal :
    n = threeBlockSize n + threeBlockSize n + threeBlockSize n + threeBlockRemainder n := by
  grind [threeBlockSize, threeBlockRemainder]

end

section
variable {n : ℕ} (hn : 6 ≤ n)
include hn

theorem threeBlockSize_fraction :
    (1 / 4 : ℝ) * n ≤ threeBlockSize n := by
  have hR : n ≤ 4 * (threeBlockSize n : ℝ) := by exact_mod_cast (by unfold threeBlockSize; omega)
  linarith

end

variable {d n m : ℕ} (h : n = m) (T : Estimator d m)

def castEstimator : Estimator d n := h.symm ▸ T

theorem castEstimator_risk_eq
    (θ : RegressionParameter d) : meanSquaredRisk (castEstimator h T) θ = meanSquaredRisk T θ := by
  subst m
  rfl

def threeBlockEstimator
    {T : (((Fin (threeBlockSize n) → Observation d) × (Fin (threeBlockSize n) → Observation d)) ×
      (Fin (threeBlockSize n) → Observation d)) → ℝ} (hmT : Measurable T) : Estimator d n :=
  castEstimator (threeBlockTotal n)
    (blockEstimatorWithRemainder hmT)

theorem threeBlockEstimator_risk_eq {C : ModelConstants d}
    {θ : RegressionParameter d} (hθ : Admissible C θ)
    (T : (((Fin (threeBlockSize n) → Observation d) × (Fin (threeBlockSize n) → Observation d)) ×
      (Fin (threeBlockSize n) → Observation d)) → ℝ) (hmT : Measurable T) :
    meanSquaredRisk (threeBlockEstimator hmT) θ =
      ∫⁻ z, ENNReal.ofReal ((T z - θ.variance) ^ 2)
        ∂((sampleLaw θ (threeBlockSize n)).prod (sampleLaw θ (threeBlockSize n))).prod
          (sampleLaw θ (threeBlockSize n)) := by
  rw [threeBlockEstimator, castEstimator_risk_eq]
  exact (sampleBlocksWithRemainder_measurePreserving hθ _ _ _ _).lintegral_comp (((hmT.sub measurable_const).pow_const 2).ennreal_ofReal)

end NearlyMinimax
