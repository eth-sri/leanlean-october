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

/-- The transition density from a larger positive start is a positive constant times the
hyperbolic state ratio and the density from the smaller start. -/
theorem conditionedPositiveTransitionDensity_eq_start_ratio_mul
    {ν t x x' y : ℝ} (hν : 0 ≤ ν) (ht : 0 < t)
    (hx' : 0 < x') (hxx' : x' ≤ x) (hy : 0 < y) :
    conditionedPositiveTransitionDensity ν t x y =
      (Real.exp (-ν * (x - x') - (x ^ 2 - x' ^ 2) / (2 * t)) *
        conditionedH ν x' / conditionedH ν x) *
        conditionedKernelParameterRatio (x' / t) (x / t) y *
          conditionedPositiveTransitionDensity ν t x' y := by
  have hx : 0 < x := lt_of_lt_of_le hx' hxx'
  have hHx := conditionedH_pos hν hx
  have hHx' := conditionedH_pos hν hx'
  have hHy := conditionedH_pos hν hy
  have hsa  :=
    Real.sinh_pos_iff.mpr (div_pos (mul_pos hx' hy) ht)
  have hsb  :=
    Real.sinh_pos_iff.mpr (div_pos (mul_pos hx hy) ht)
  have hheatx := brownianHeatDensity_sub_factor ht (x := x) (y := y)
  have hheatx' := brownianHeatDensity_sub_factor ht (x := x') (y := y)
  simp only [conditionedPositiveTransitionDensity, hν, ht, hx, hx', hy,
    and_self, ite_true]
  rw [hheatx, hheatx']
  simp only [conditionedKernelParameterRatio]
  field_simp [hHx.ne', hHx'.ne', hHy.ne', hsa.ne', hsb.ne', ht.ne']
  simp_rw [← Real.exp_add]
  apply congrArg Real.exp
  field_simp [ht.ne']
  ring_nf

/-- For fixed positive time and nonnegative drift, the transition density ratio from ordered
positive start states is nondecreasing in the endpoint, including the BES(3) zero-drift case. -/
theorem conditionedPositiveTransitionDensity_start_ratio_monotoneOn_state
    {ν t x x' : ℝ} (hν : 0 ≤ ν) (ht : 0 < t)
    (hx' : 0 < x') (hxx' : x' ≤ x) :
    MonotoneOn
      (fun y => conditionedPositiveTransitionDensity ν t x y /
        conditionedPositiveTransitionDensity ν t x' y) (Set.Ioi 0) := by
  have hx  := lt_of_lt_of_le hx' hxx'
  have hratio := conditionedKernelParameterRatio_monotoneOn_state
    (div_pos hx' ht) ((div_le_div_iff_of_pos_right ht).2 hxx')
  have hconst : 0 < Real.exp (-ν * (x - x') - (x ^ 2 - x' ^ 2) / (2 * t)) *
      conditionedH ν x' / conditionedH ν x := div_pos (mul_pos (Real.exp_pos _) (conditionedH_pos hν hx'))
      (conditionedH_pos hν hx)
  have hfactor (y : ℝ) (hy : 0 < y) :
      conditionedPositiveTransitionDensity ν t x y /
        conditionedPositiveTransitionDensity ν t x' y =
          (Real.exp (-ν * (x - x') - (x ^ 2 - x' ^ 2) / (2 * t)) *
            conditionedH ν x' / conditionedH ν x) *
            conditionedKernelParameterRatio (x' / t) (x / t) y := by
    rw [conditionedPositiveTransitionDensity_eq_start_ratio_mul hν ht hx' hxx' hy]
    have hden := conditionedPositiveTransitionDensity_pos hν ht hx' hy
    field_simp [hden.ne']
  intro y₁ hy₁ y₂ hy₂ hyy
  have hy₁' : 0 < y₁ := by simpa using hy₁
  have hy₂' : 0 < y₂ := by simpa using hy₂
  change conditionedPositiveTransitionDensity ν t x y₁ /
      conditionedPositiveTransitionDensity ν t x' y₁ ≤
    conditionedPositiveTransitionDensity ν t x y₂ /
      conditionedPositiveTransitionDensity ν t x' y₂
  rw [hfactor y₁ hy₁', hfactor y₂ hy₂']
  exact mul_le_mul_of_nonneg_left (hratio hy₁' hy₂' hyy) (le_of_lt hconst)

end DOZZ.Proofs

end
