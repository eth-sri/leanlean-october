/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelScores

/-!
# Parameter derivative of the conditioned-kernel score

The ordered coupling needs the score to be increasing and one-Lipschitz in its drift parameter.
This file proves the derivative formula and its pointwise bounds away from the zero-parameter
limit.
-/

@[expose] public section

open Filter Topology

namespace DOZZ.Proofs

/-- The derivative of `a ↦ a coth (a*y)` in the positive parameter regime. -/
noncomputable def conditionedKernelScoreParameterSlope (a y : ℝ) : ℝ :=
  (Real.sinh (a * y) * Real.cosh (a * y) - a * y) / Real.sinh (a * y) ^ 2

section
variable {a y : ℝ} (ha : 0 < a) (hy : 0 < y)
include ha hy

/-- Derivative of the conditioned-kernel score in its parameter. -/
theorem hasDerivAt_conditionedKernelScore_parameter :
    HasDerivAt (fun x : ℝ => conditionedKernelScore x y)
      (conditionedKernelScoreParameterSlope a y) a := by
  have h : HasDerivAt (fun x => x * y) y a := by
    simpa using (hasDerivAt_id a).mul_const y
  convert (hasDerivAt_id a).mul ((hasDerivAt_cosh_div_sinh (mul_ne_zero ha.ne' hy.ne')).comp a h) using 1
  · ext x
    simp [conditionedKernelScore, mul_div_assoc]
  · dsimp [conditionedKernelScoreParameterSlope, Function.comp_def]
    field

/-- The score parameter derivative lies between zero and one. -/
theorem conditionedKernelScoreParameterSlope_bounds :
    0 ≤ conditionedKernelScoreParameterSlope a y ∧
      conditionedKernelScoreParameterSlope a y ≤ 1 := by
  let u := a * y
  have hu : 0 < u := mul_pos ha hy
  have hs := Real.sinh_pos_iff.mpr hu
  change 0 ≤ (Real.sinh u * Real.cosh u - u) / Real.sinh u ^ 2 ∧
    (Real.sinh u * Real.cosh u - u) / Real.sinh u ^ 2 ≤ 1
  constructor
  · exact div_nonneg (sub_nonneg.mpr ((Real.self_le_sinh_iff.mpr hu.le).trans
      (le_mul_of_one_le_right hs.le (Real.one_le_cosh u)))) (sq_nonneg _)
  · apply (div_le_one (sq_pos_of_pos hs)).mpr
    have hp : Real.sinh u * Real.exp (-u) = (1 - Real.exp (-2 * u)) / 2 := by
      rw [Real.sinh_eq, sub_div, sub_mul, div_mul_eq_mul_div, div_mul_eq_mul_div,
        ← Real.exp_add, ← Real.exp_add]
      ring_nf
      simp
    have hb := congrArg (Real.sinh u * ·) (Real.cosh_sub_sinh u)
    nlinarith [Real.add_one_le_exp (-2 * u)]

end

/-- The conditioned-kernel score has the continuous zero-parameter limit `1/y`. -/
theorem conditionedKernelScore_tendsto_zero_parameter
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun a : ℝ => conditionedKernelScore a y)
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / y)) := by
  have hxy : Tendsto (fun a : ℝ => a * y) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun a : ℝ => a * y) := by fun_prop
    simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hden_ne : ∀ᶠ a : ℝ in 𝓝[≠] (0 : ℝ), a * y ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    exact mul_ne_zero (by simpa using ha) hy.ne'
  have hratio := (Asymptotics.isEquivalent_iff_tendsto_one hden_ne).mp
      (Real.isEquivalent_sinh.comp_tendsto hxy)
  have hcosh : Tendsto (fun a : ℝ => Real.cosh (a * y))
      (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have h := (Real.continuous_cosh.tendsto (0 : ℝ)).comp hxy
    simpa [Function.comp_def] using h
  have hscaled : Tendsto
      (fun a : ℝ => Real.cosh (a * y) / (Real.sinh (a * y) / (a * y)) * (1 / y))
      (𝓝[≠] (0 : ℝ)) (𝓝 (1 / y)) := by
    have h := (hcosh.div hratio (by norm_num)).mul_const (1 / y)
    simpa using h
  have heq : (fun a : ℝ => conditionedKernelScore a y) =ᶠ[𝓝[≠] (0 : ℝ)]
      (fun a => Real.cosh (a * y) / (Real.sinh (a * y) / (a * y)) * (1 / y)) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha0 : a ≠ 0 := by simpa using ha
    have hsne  :=
      Real.sinh_ne_zero.mpr (mul_ne_zero ha0 hy.ne')
    dsimp [conditionedKernelScore]
    field_simp [ha0, hy.ne', hsne]
  exact hscaled.congr' heq.symm

/-- Increasing the positive parameter increases the score by at most the parameter increment. -/
theorem conditionedKernelScore_increment_bounds
    {a b y : ℝ} (ha : 0 < a) (hy : 0 < y) (hab : a ≤ b) :
    0 ≤ conditionedKernelScore b y - conditionedKernelScore a y ∧
      conditionedKernelScore b y - conditionedKernelScore a y ≤ b - a := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hd (x : ℝ) (hx : a ≤ x) := hasDerivAt_conditionedKernelScore_parameter (ha.trans_le hx) hy
  obtain ⟨x, hx, h⟩ := exists_hasDerivAt_eq_slope _ _ hab
    (fun x hx => (hd x hx.1).continuousAt.continuousWithinAt)
    (fun x hx => hd x hx.1.le)
  have hb := conditionedKernelScoreParameterSlope_bounds (ha.trans hx.1) hy
  rw [h] at hb
  exact ⟨(by simpa using (le_div_iff₀ (sub_pos.mpr hab)).mp hb.1),
    (div_le_one (sub_pos.mpr hab)).mp hb.2⟩

/-- Combining state antitonicity with the one-Lipschitz parameter bound controls a mixed
parameter-and-state increment. This is the score estimate in the shifted-density comparison for
the upper quantile bound. -/
theorem conditionedKernelScore_mixed_increment_upper
    {a b y z : ℝ} (ha : 0 < a) (hy : 0 < y) (hyz : y ≤ z) (hab : a ≤ b) :
    conditionedKernelScore b z - conditionedKernelScore a y ≤ b - a := by
  have h := (conditionedKernelScore_strictAntiOn_state (ha.trans_le hab)).antitoneOn hy
    (hy.trans_le hyz) hyz
  linarith [(conditionedKernelScore_increment_bounds ha hy hab).2]

end DOZZ.Proofs

end
