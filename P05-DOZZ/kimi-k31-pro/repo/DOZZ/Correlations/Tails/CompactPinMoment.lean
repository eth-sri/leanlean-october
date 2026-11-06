/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Correlations.Tails.PinEnvelopeMoment

/-! Uniform Gaussian correction moments over the compact insertion-center geometry. -/


open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs

/-- Compact exterior centers give uniform pin variance and inverse-variance bounds. -/
theorem compact_pin_parameters (K : Set ℂ) (hK : IsCompact K)
    (hz : ∀ z ∈ K, 2 ≤ ‖z‖) (γ : ℝ) :
    ∃ v a : ℝ, 0 ≤ v ∧ 0 ≤ a ∧ ∀ z ∈ K,
      2 * Real.log ‖z‖ ≤ v ∧ |γ| / (2 * Real.log ‖z‖) ≤ a := by
  rcases K.eq_empty_or_nonempty with he | hn
  · exact ⟨0, 0, le_rfl, le_rfl, by simp [he]⟩
  obtain ⟨zmax, hzmax, hmax⟩ := hK.exists_isMaxOn hn continuous_norm.continuousOn
  refine ⟨2 * Real.log ‖zmax‖, |γ| / (2 * Real.log 2),
    (offCenter_pin_variance_pos zmax (hz zmax hzmax)).le,
    div_nonneg (abs_nonneg γ) (by positivity), ?_⟩
  intro z hzk
  have hlog2 : Real.log 2 ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) (hz z hzk)
  have hlogmax : Real.log ‖z‖ ≤ Real.log ‖zmax‖ :=
    Real.log_le_log (by linarith [hz z hzk]) (hmax hzk)
  exact ⟨by linarith, div_le_div_of_nonneg_left (abs_nonneg γ)
    (by positivity) (by linarith)⟩

end DOZZ.Proofs
