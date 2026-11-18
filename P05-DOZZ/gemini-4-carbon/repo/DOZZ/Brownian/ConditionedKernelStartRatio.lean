/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelParameterRatio

/-!
# Monotone likelihood ratio in the start state

For fixed nonnegative drift, changing the positive start state contributes the increasing
hyperbolic ratio `sinh((x/t)y)/sinh((x'/t)y)`. This is the start-order density comparison used in
the explicit-kernel coupling argument.
-/

@[expose] public section

namespace DOZZ.Proofs





/-- For fixed positive time and nonnegative drift, the transition density ratio from ordered
positive start states is nondecreasing in the endpoint, including the BES(3) zero-drift case. -/
theorem conditionedPositiveTransitionDensity_start_ratio_monotoneOn_state
    {ν t x x' : ℝ} (hν : 0 ≤ ν) (ht : 0 < t)
    (hx' : 0 < x') (hxx' : x' ≤ x) :
    MonotoneOn
      (fun y => conditionedPositiveTransitionDensity ν t x y /
        conditionedPositiveTransitionDensity ν t x' y) (Set.Ioi 0) := by
  have brownianHeatDensity_sub_factor {x y : ℝ} : brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) =
        Real.exp (-(x ^ 2 + y ^ 2) / (2 * t)) *
          (2 * Real.sinh (x * y / t) / Real.sqrt (2 * Real.pi * t)) := by
    have he₁ : -((y - x) ^ 2) / (2 * t) =
        -(x ^ 2 + y ^ 2) / (2 * t) + x * y / t := by ring
    have he₂ : -((y + x) ^ 2) / (2 * t) =
        -(x ^ 2 + y ^ 2) / (2 * t) + -(x * y / t) := by ring
    have hden : Real.sqrt (2 * Real.pi * t) ≠ 0 := by positivity
    simp only [brownianHeatDensity, ht, ite_true]
    rw [he₁, he₂, Real.exp_add, Real.exp_add]
    rw [Real.sinh_eq]
    field_simp [hden]
  have conditionedH_pos_of_nonneg {x : ℝ} (hx : 0 < x) : 0 < conditionedH ν x := by
    by_cases hzero : ν = 0
    · simp [conditionedH, hzero, hx]
    · simp only [conditionedH, ite_eq_right hzero]
      apply sub_pos.mpr
      have := lt_of_le_of_ne hν (Ne.symm hzero)
      apply (Real.exp_lt_one_iff).2
      nlinarith
  have conditionedPositiveTransitionDensity_pos_of_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : 0 < conditionedPositiveTransitionDensity ν t x y := by
    have hHₓ := conditionedH_pos_of_nonneg hx
    have hHᵧ := conditionedH_pos_of_nonneg hy
    have : 0 < brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x) := by
      rw [brownianHeatDensity_sub_factor]
      have :=
        Real.sinh_pos_iff.mpr (div_pos (mul_pos hx hy) ht)
      positivity
    simp only [conditionedPositiveTransitionDensity, hν, ht, hx, hy,
      and_self, ite_true]
    positivity
  have conditionedPositiveTransitionDensity_eq_start_ratio_mul {y : ℝ} (hy : 0 < y) : conditionedPositiveTransitionDensity ν t x y =
        (Real.exp (-ν * (x - x') - (x ^ 2 - x' ^ 2) / (2 * t)) *
          conditionedH ν x' / conditionedH ν x) *
          conditionedKernelParameterRatio (x' / t) (x / t) y *
            conditionedPositiveTransitionDensity ν t x' y := by
    have hx := lt_of_lt_of_le hx' hxx'
    have hHx := conditionedH_pos_of_nonneg hx
    have hHx' := conditionedH_pos_of_nonneg hx'
    have hheatx := brownianHeatDensity_sub_factor (x := x) (y := y)
    have hheatx' := brownianHeatDensity_sub_factor (x := x') (y := y)
    simp only [conditionedPositiveTransitionDensity, hν, ht, hx, hx', hy,
      and_self, ite_true]
    rw [hheatx, hheatx']
    simp only [conditionedKernelParameterRatio]
    field_simp [hHx.ne', hHx'.ne', (conditionedH_pos_of_nonneg hy).ne', (Real.sinh_pos_iff.mpr (div_pos (mul_pos hx' hy) ht)).ne', (Real.sinh_pos_iff.mpr (div_pos (mul_pos hx hy) ht)).ne', ht.ne']
    simp_rw [← Real.exp_add]
    apply congrArg Real.exp
    field_simp [ht.ne']
    ring_nf
  have hx := lt_of_lt_of_le hx' hxx'
  have hratio := conditionedKernelParameterRatio_monotoneOn_state
    (div_pos hx' ht) ((div_le_div_iff_of_pos_right ht).2 hxx')
  have hconst : 0 < Real.exp (-ν * (x - x') - (x ^ 2 - x' ^ 2) / (2 * t)) *
      conditionedH ν x' / conditionedH ν x := div_pos (mul_pos (Real.exp_pos _) (conditionedH_pos_of_nonneg hx'))
      (conditionedH_pos_of_nonneg hx)
  have hfactor (y : ℝ) (hy : 0 < y) :
      conditionedPositiveTransitionDensity ν t x y /
        conditionedPositiveTransitionDensity ν t x' y =
          (Real.exp (-ν * (x - x') - (x ^ 2 - x' ^ 2) / (2 * t)) *
            conditionedH ν x' / conditionedH ν x) *
            conditionedKernelParameterRatio (x' / t) (x / t) y := by
    rw [conditionedPositiveTransitionDensity_eq_start_ratio_mul hy]
    field_simp [(conditionedPositiveTransitionDensity_pos_of_nonneg hx' hy).ne']
  intro y₁ hy₁ y₂ hy₂ hyy
  have hy₁' : 0 < y₁ := by assumption
  have hy₂' : 0 < y₂ := by assumption
  change conditionedPositiveTransitionDensity ν t x y₁ /
      conditionedPositiveTransitionDensity ν t x' y₁ ≤
    conditionedPositiveTransitionDensity ν t x y₂ /
      conditionedPositiveTransitionDensity ν t x' y₂
  rw [hfactor y₁ hy₁', hfactor y₂ hy₂']
  exact mul_le_mul_of_nonneg_left (hratio hy₁' hy₂' hyy) (le_of_lt hconst)

end DOZZ.Proofs

end
