/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Definitions
public import BergmanWeakType.Kernel

/-! # Comparison and test functions for weak type constants -/

public section

open MeasureTheory Set Filter
open scoped ENNReal

namespace BergmanWeakType

variable {μ : Measure ℂ} {T : (ℂ → ℂ) → ℂ → ℝ≥0∞} {C : ℝ≥0∞}

theorem IsWeakTypeBound.test_le (hC : IsWeakTypeBound μ T C) {f : ℂ → ℂ}
    (hf : Integrable f μ) {E : Set ℂ} {l : ℝ}
    (h : ∀ᵐ z ∂μ, z ∈ E → ENNReal.ofReal l ≤ T f z) :
    ENNReal.ofReal l * μ E ≤ C * ∫⁻ z, ‖f z‖ₑ ∂μ := by
  by_cases hl : l ≤ 0
  · simp [ENNReal.ofReal_eq_zero.mpr hl]
  have hp := lt_of_not_ge hl
  apply le_of_tendsto (ENNReal.Tendsto.mul_const
    (ENNReal.continuous_ofReal.continuousWithinAt (s := Iio l)) (Or.inl (by positivity)))
  filter_upwards [Ioo_mem_nhdsLT hp] with t ht
  refine (mul_le_mul_right (measure_mono_ae (h.mono fun z hz hzE ↦ ?_)) _).trans (hC f hf t ht.1)
  exact ((ENNReal.ofReal_lt_ofReal_iff hp).mpr ht.2).trans_le (hz hzE)

/-- Test on an indicator and cancel its positive finite input mass. -/
theorem IsWeakTypeBound.test_indicator [IsFiniteMeasure μ] (hC : IsWeakTypeBound μ T C)
    {s E : Set ℂ} (hs : MeasurableSet s) (hpos : μ s ≠ 0) {l : ℝ} (hl : 0 ≤ l)
    (hout : ∀ᵐ z ∂μ, z ∈ E → ENNReal.ofReal (l * μ.real s) ≤ T (s.indicator (fun _ ↦ 1)) z) :
    ENNReal.ofReal l * μ E ≤ C := by
  have h := hC.test_le ((integrable_const (1 : ℂ)).indicator hs) hout
  have hmass : (∫⁻ z, ‖s.indicator (fun _ ↦ (1 : ℂ)) z‖ₑ ∂μ) = μ s := by
    simp [enorm_indicator_eq_indicator_enorm, hs]
  rw [hmass, ENNReal.ofReal_mul hl, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top μ s), mul_right_comm] at h
  exact (ENNReal.mul_le_mul_iff_left hpos (measure_ne_top μ s)).mp h

end BergmanWeakType
