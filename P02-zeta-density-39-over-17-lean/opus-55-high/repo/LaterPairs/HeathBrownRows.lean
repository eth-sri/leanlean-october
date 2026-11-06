module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
open Expdb
open scoped NNReal
namespace TaoTrudgianYang2025
theorem heathBrownBetaBound_five_first {α : ℝ}
    (hα : α ≤ 1/4) :
    heathBrownBetaBound 5 α = 1/20+3/4*α := by
  pm_1536
  have hfirst : max (α*(19/20)) (α-1/50) ≤ 1/20+α*(3/4) :=
    max_le (by linarith) (by linarith)
  rw [max_eq_left hfirst]
  ring

theorem heathBrownBetaBound_five_second {α : ℝ}
    (hα : 1/4 ≤ α) (hα₁ : α ≤ 2/5) :
    heathBrownBetaBound 5 α = 19/20*α := by
  pm_1536
  rw [max_eq_left (by linarith : α-1/50 ≤ α*(19/20))]
  rw [max_eq_right (by linarith : 1/20+α*(3/4) ≤ α*(19/20))]
  ring

section
variable {α : ℝ≥0}
include α
theorem exponentSumGrowthExponent_le_heathBrown_firstRow (hα : (α : ℝ) ≤ 1/4) :
    exponentSumGrowthExponent α ≤ 1/20+3/4*(α : ℝ) := by
  by_cases hpos : 0 < (α : ℝ)
  · have h := exponentSumGrowthExponent_le_heathBrown_of_derivative
      GafniTao.heathBrownKthDerivativeTheorem_native
      (by norm_num : 3 ≤ (5 : ℕ)) hpos
    rw [heathBrownBetaBound_five_first hα] at h
    exact h
  · have hz : α = 0 := NNReal.coe_injective (le_antisymm (le_of_not_gt hpos) α.coe_nonneg)
    subst α
    rw [exponentSumGrowthExponent_zero]
    norm_num

theorem exponentSumGrowthExponent_le_heathBrown_secondSegment (hα : 1/4 ≤ (α : ℝ)) (hα₁ : (α : ℝ) ≤ 2/5) :
    exponentSumGrowthExponent α ≤ 19/20*(α : ℝ) := by
  have h := exponentSumGrowthExponent_le_heathBrown_of_derivative
    GafniTao.heathBrownKthDerivativeTheorem_native
    (by norm_num : 3 ≤ (5 : ℕ)) (by linarith : 0 < (α : ℝ))
  rw [heathBrownBetaBound_five_second hα hα₁] at h
  exact h

theorem exponentSumGrowthExponent_le_heathBrown_secondRow (hα : 1/4 ≤ (α : ℝ)) (hα₁ : (α : ℝ) ≤ 890/3277) :
    exponentSumGrowthExponent α ≤ 19/20*(α : ℝ) :=
  exponentSumGrowthExponent_le_heathBrown_secondSegment hα (by linarith)
end
end TaoTrudgianYang2025
