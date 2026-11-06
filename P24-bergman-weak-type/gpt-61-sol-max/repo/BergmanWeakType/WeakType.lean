/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/

import BergmanWeakType.Definitions
import Mathlib.Tactic

/-! # Comparison and test functions for weak type constants -/




open MeasureTheory
open scoped ENNReal

namespace BergmanWeakType

variable {μ : Measure ℂ} {T : (ℂ → ℂ) → ℂ → ℝ≥0∞} {C : ℝ≥0∞}

theorem IsWeakTypeBound.mul_measure_le_of_ae_lower
    (hC : IsWeakTypeBound μ T C) {f } (hf : Integrable f μ)
    {t } (ht : t ≠ ∞) {E : Set ℂ}
    (hsub : ∀ᵐ z ∂μ, z ∈ E → t ≤ T f z) :
    t * μ E ≤ C * ∫⁻ z, ‖f z‖ₑ ∂μ := by
  by_cases ht0 : t = 0
  · continuity
  apply ENNReal.le_of_forall_lt_one_mul_le
  intro a ha
  by_cases ha0 : a = 0
  · continuity
  have hat := ENNReal.mul_ne_top (ne_top_of_lt ha) ht
  have hb := hC f hf _ (ENNReal.toReal_pos (mul_ne_zero ha0 ht0) hat)
  rw [ENNReal.ofReal_toReal hat] at hb
  simpa [mul_assoc] using
    (mul_le_mul_right (measure_mono_ae (by
      filter_upwards [hsub] with z hz
      intro hzE
      apply lt_of_lt_of_le _ (hz hzE)
      simpa using ENNReal.mul_lt_mul_left ht0 ht ha
    )) _).trans hb

theorem IsWeakTypeBound.le_of_indicator [IsFiniteMeasure μ]
    (hC : IsWeakTypeBound μ T C) {s E : Set ℂ} (hs : MeasurableSet s)
    (hpos : μ s ≠ 0) {t } (ht : 0 < t)
    (hsub : ∀ᵐ z ∂μ, z ∈ E → ENNReal.ofReal (t * μ.real s) ≤ T (s.indicator (fun _ ↦ 1)) z) :
    ENNReal.ofReal t * μ E ≤ C := by
  have hfin := measure_ne_top μ s
  have hb := hC.mul_measure_le_of_ae_lower ((integrable_const _).indicator hs)
    ENNReal.ofReal_ne_top hsub
  simp [enorm_indicator_eq_indicator_enorm, hs,
    ENNReal.ofReal_mul ht.le] at hb
  apply (ENNReal.mul_le_mul_iff_right hpos hfin).mp
  simpa [mul_assoc, mul_comm, mul_left_comm] using hb

theorem measure_univ_div_mass_le_weakTypeConstant_of_witness {f : ℂ → ℂ}
    (hf : Integrable f μ) (hout : ∀ᵐ z ∂μ, 1 ≤ T f z) : μ Set.univ / ∫⁻ z, ‖f z‖ₑ ∂μ ≤ weakTypeConstant μ T :=
  by
  refine le_sInf fun C hC ↦ ENNReal.div_le_of_le_mul ?_
  simpa using! (hC.mul_measure_le_of_ae_lower hf ENNReal.one_ne_top (hout.mono fun _ hz _ ↦ hz))

end BergmanWeakType
