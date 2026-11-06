/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Analytic.RetainedComplement

/-! Exact additive mass increments on nested measurable retained sets. -/

@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace DOZZ.Proofs
section
variable (μ : Measure ℂ) (w : ℂ → ℝ≥0∞) (O₀ O₁ : Set ℂ)
section
variable (h₀ : MeasurableSet O₀) (h₁ : MeasurableSet O₁) (hsub : O₀ ⊆ O₁)
include h₀ h₁ hsub

/-- The mass added between nested sets is their weighted set-difference mass. -/
theorem nested_weighted_mass_add :
    (∫⁻ x in O₀, w x ∂μ) + (∫⁻ x in O₁ \ O₀, w x ∂μ) = ∫⁻ x in O₁, w x ∂μ := by
  have he := measure_inter_add_sdiff (μ := μ.withDensity w) O₁ h₀
  rw [Set.inter_eq_right.mpr hsub,
    withDensity_apply _ h₀, withDensity_apply _ (h₁.diff h₀), withDensity_apply _ h₁] at he
  exact he

/-- Finite full mass makes the nested mass decomposition valid after taking real values. -/
theorem nested_weighted_mass_real (hfin : (∫⁻ x, w x ∂μ) ≠ ⊤) :
    (∫⁻ x in O₀, w x ∂μ).toReal + (∫⁻ x in O₁ \ O₀, w x ∂μ).toReal =
        (∫⁻ x in O₁, w x ∂μ).toReal ∧
      (∫⁻ x in O₁, w x ∂μ).toReal ≤ (∫⁻ x, w x ∂μ).toReal := by
  constructor
  · rw [← ENNReal.toReal_add (ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral O₀ w)) (ne_top_of_le_ne_top hfin (setLIntegral_le_lintegral (O₁ \ O₀) w)),
      nested_weighted_mass_add μ w O₀ O₁ h₀ h₁ hsub]
  · exact ENNReal.toReal_mono hfin (setLIntegral_le_lintegral O₁ w)

end

end

end DOZZ.Proofs
