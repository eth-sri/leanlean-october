/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Correlations.BridgeMultiplicity

/-! Exact tail-error margins on the residue domain (erratum K30, see
docs/ERRATA-AND-DEVIATIONS.md). -/

@[expose] public section
open MeasureTheory Filter Topology Set
namespace DOZZ.Proofs
section
variable (γ α : ℝ)
section
variable (hγ : 0 < γ) (hα : γ / 2 < α) (hαQ : α < Q γ)
include hγ hα hαQ

/-- The critical order is strictly below the bulk threshold, including on the branch (erratum K30,
see docs/ERRATA-AND-DEVIATIONS.md) where the smaller charge need not exceed gamma/2. -/
theorem residue_critical_order_bounds :
    0 < reflectionExponent γ α ∧ reflectionExponent γ α < 4 / γ ^ 2 := by
  have hp : 0 < reflectionExponent γ α := by unfold reflectionExponent; positivity
  have he : 4 / γ ^ 2 - reflectionExponent γ α = 2 * (α - γ / 2) / γ := by
    unfold reflectionExponent Q
    ring
  have hg : 0 < 2 * (α - γ / 2) / γ := by positivity
  grind

/-- A one-root tail always has a positive admissible error on the physical charge interval. -/
theorem residue_oneInsertionErrorCeiling_pos : 0 < oneInsertionErrorCeiling γ α := by
  obtain ⟨hp, hpbulk⟩ := residue_critical_order_bounds γ α hγ hα hαQ
  have hceil : reflectionExponent γ α < oneInsertionMomentCeiling γ α := by
    unfold oneInsertionMomentCeiling
    simp_all
  unfold oneInsertionErrorCeiling
  bound

/-- The two-root equal-charge tail has a strict error above the common critical order. -/
theorem residue_equal_twoInsertionTailCeiling_gt :
    reflectionExponent γ α < twoInsertionTailCeiling γ α α := by
  have he := residue_oneInsertionErrorCeiling_pos γ α hγ hα hαQ
  have hl : 0 < twoInsertionPointLoss γ α α := by
    unfold twoInsertionPointLoss
    positivity
  unfold twoInsertionTailCeiling
  simp_all

end

end

/-- The smaller-charge singularity is strictly above the critical order whenever unequal,
without adding the printed alpha2>gamma/2 restriction. -/
theorem residue_unequal_threshold_gap (γ α2 α3 : ℝ) (hγ : 0 < γ)
    (hα2 : 0 < α2) (hα23 : α2 < α3) (hα3 : γ / 2 < α3) :
    0 < min (2 * (α3 - γ / 2) / γ)
      (min (2 * α2 / γ) (2 * (α3 - α2) / γ)) := by positivity

end DOZZ.Proofs
