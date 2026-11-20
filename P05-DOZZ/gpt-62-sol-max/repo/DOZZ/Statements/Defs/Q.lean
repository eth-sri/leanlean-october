/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Distribution.Distribution
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Topology.ContinuousMap.Bounded.Basic
public import Mathlib.Topology.DiscreteSubset

/-! The definition `DOZZ.Q`. -/

@[expose] public section

open Complex MeasureTheory Set Filter Topology

namespace DOZZ

/-- `Q = 2/γ + γ/2` ([KRV, (valueQ)]). -/
noncomputable def Q (γ : ℝ) : ℝ := 2 / γ + γ / 2

/-- The two shift lengths are ordered throughout the physical coupling interval. -/
theorem half_gamma_lt_two_div {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) : γ / 2 < 2 / γ :=
  (div_lt_div_iff₀ two_pos hγ).2 (mul_self_lt_mul_self hγ.le hγ₂)

/-- The physical reflection interval contains the charge `γ`. -/
theorem gamma_lt_Q {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) : γ < Q γ := by
  have := half_gamma_lt_two_div hγ hγ₂
  dsimp [Q]
  linarith

theorem Q_pos {γ : ℝ} (hγ : 0 < γ) : 0 < Q γ :=
  add_pos (div_pos two_pos hγ) (half_pos hγ)

theorem two_lt_Q {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) : 2 < Q γ := by
  rw [Q, ← sub_pos, show 2 / γ + γ / 2 - 2 = (γ - 2) ^ 2 / (2 * γ) by field_simp; ring]
  exact div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hγ₂.ne)) (mul_pos two_pos hγ)

end DOZZ
