/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import BergmanWeakType.Weighted.CompactIntegral
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-! Angular integration as integration against a probability measure. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Real

namespace BergmanWeakType

/-- The radial interval of the disk and its interior, also used for radial mass. -/
abbrev radii : Set ℝ := Ico 0 1
abbrev openRadii : Set ℝ := Ioo 0 1
abbrev angleDomain : Set ℝ := Icc (-π) π

theorem sq_lt_one_of_mem_Ico {r : ℝ} (hr : r ∈ radii) : r ^ 2 < 1 := by
  simpa using (sq_lt_sq₀ hr.1 zero_le_one).mpr hr.2

theorem radial_defect_pos {r : ℝ} (hr : r ∈ radii) : 0 < 1 - r ^ 2 :=
  sub_pos.mpr (sq_lt_one_of_mem_Ico hr)

def angleMeasure : Measure ℝ :=
  ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Ioo (-π) π)

instance : IsProbabilityMeasure angleMeasure where
  measure_univ := by
    rw [angleMeasure, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      Real.volume_Ioo, sub_neg_eq_add, ← two_mul, ← ENNReal.ofReal_mul (inv_nonneg.mpr two_pi_pos.le),
      inv_mul_cancel₀ two_pi_pos.ne', ENNReal.ofReal_one]

instance : NullSingletonClass angleMeasure where
  measure_singleton θ := by
    simp [angleMeasure]

theorem ae_mem_angle_open : ∀ᵐ θ ∂angleMeasure, θ ∈ Ioo (-π) π :=
  Measure.ae_smul_measure (ae_restrict_mem measurableSet_Ioo) _

theorem ae_mem_angle : ∀ᵐ θ ∂angleMeasure, θ ∈ angleDomain :=
  ae_mem_angle_open.mono fun _ h ↦ Ioo_subset_Icc_self h

theorem integral_angleMeasure_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : ∫ θ, f θ ∂angleMeasure = (2 * π)⁻¹ • ∫ θ in -π..π, f θ := by
  rw [angleMeasure, integral_smul_measure, ENNReal.toReal_ofReal (by positivity),
    intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo]

theorem circleAverage_eq_integral_angleMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (c : ℂ) (r : ℝ) :
    circleAverage f c r = ∫ θ, f (circleMap c r θ) ∂angleMeasure := by
  rw [circleAverage_eq_integral_add (-π),
    intervalIntegral.integral_comp_add_right (fun θ ↦ f (circleMap c r θ)) (-π),
    zero_add, show 2 * π + -π = π by ring, integral_angleMeasure_eq]

end BergmanWeakType
