/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Brownian.ConditionedPositiveTransitionDensity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Shared pointwise identities for the killed heat kernel and its Doob transform. -/

@[expose] public section

namespace DOZZ.Proofs

theorem conditionedH_pos {ν x : ℝ} (hν : 0 ≤ ν) (hx : 0 < x) :
    0 < conditionedH ν x := by
  rcases hν.eq_or_lt with rfl | hp
  · simpa [conditionedH] using hx
  · rw [conditionedH, ite_eq_right hp.ne']
    exact sub_pos.mpr (Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hp hx]))

theorem brownianHeatDensity_even (t : ℝ) : Function.Even (brownianHeatDensity t) := by
  intro z
  simp [brownianHeatDensity]

section
variable {t x y : ℝ} (ht : 0 < t)
include ht

theorem brownianHeatDensity_sub_factor :
    brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) =
      Real.exp (-(x ^ 2 + y ^ 2) / (2 * t)) *
        (2 * Real.sinh (x * y / t) / Real.sqrt (2 * Real.pi * t)) := by
  have hl : -((y - x) ^ 2) / (2 * t) =
      -(x ^ 2 + y ^ 2) / (2 * t) + x * y / t := by field_simp; ring
  have hr : -((y + x) ^ 2) / (2 * t) =
      -(x ^ 2 + y ^ 2) / (2 * t) + -(x * y / t) := by field_simp; ring
  simp only [brownianHeatDensity, ite_eq_left ht, hl, hr, Real.exp_add, Real.sinh_eq]
  ring

theorem brownianHeatDensity_sub_pos (hx : 0 < x) (hy : 0 < y) :
    0 < brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) := by
  rw [brownianHeatDensity_sub_factor ht]
  positivity

end

theorem conditionedPositiveTransitionDensity_pos {ν t x y : ℝ}
    (hν : 0 ≤ ν) (ht : 0 < t) (hx : 0 < x) (hy : 0 < y) :
    0 < conditionedPositiveTransitionDensity ν t x y := by
  rw [conditionedPositiveTransitionDensity, ite_eq_left ⟨hν, ht, hx, hy⟩]
  have := brownianHeatDensity_sub_pos ht hx hy
  have := conditionedH_pos hν hx
  have := conditionedH_pos hν hy
  positivity

theorem conditionedH_eq_sinh {ν x : ℝ} (hν : 0 < ν) :
    conditionedH ν x = 2 * Real.exp (-(ν * x)) * Real.sinh (ν * x) := by
  rw [conditionedH, ite_eq_right hν.ne', Real.sinh_eq]
  calc
    _ = Real.exp (-(ν * x) + ν * x) - Real.exp (-(ν * x) + -(ν * x)) := by
      rw [neg_add_cancel, Real.exp_zero]
      congr 2 <;> ring
    _ = _ := by rw [Real.exp_add, Real.exp_add]; ring

theorem brownianHeatDensity_mul_exp {t a z w : ℝ} (ht : 0 < t)
    (h : a - z ^ 2 / (2 * t) = -(w ^ 2) / (2 * t)) :
    Real.exp a * brownianHeatDensity t z = brownianHeatDensity t w := by
  simp only [brownianHeatDensity, ite_eq_left ht, ← mul_div_assoc, ← Real.exp_add, neg_div, ← sub_eq_add_neg, h]

theorem brownianHeatDensity_tilt {t ν z : ℝ} (ht : 0 < t) :
    Real.exp (ν * z - ν ^ 2 * t / 2) * brownianHeatDensity t z =
      brownianHeatDensity t (z - ν * t) := by
  apply brownianHeatDensity_mul_exp ht
  field_simp
  ring

theorem brownianHeatDensity_opposite_drift (ν z t : ℝ) (ht : 0 < t) :
    Real.exp (2 * ν * z) * brownianHeatDensity t (z + ν * t) =
      brownianHeatDensity t (z - ν * t) := by
  apply brownianHeatDensity_mul_exp ht
  field_simp
  ring

end DOZZ.Proofs

end
