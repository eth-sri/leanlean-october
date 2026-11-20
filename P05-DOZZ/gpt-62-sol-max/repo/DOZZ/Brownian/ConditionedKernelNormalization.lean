/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Brownian.ConditionedKernelGaussianIntegrals

/-!
# Normalization of the explicit conditioned transition kernel

The positive-drift transition density is expanded into four translated Gaussian terms. Pairing
the two terms with opposite shifts gives its total mass by the half-line Gaussian identity.
-/

@[expose] public section

open MeasureTheory Set

namespace DOZZ.Proofs

/-- For positive drift and positive start, the explicit transition density integrates to one. -/
theorem conditionedPositiveTransitionDensity_integral_eq_one_pos
    {ν t x : ℝ} (hν : 0 < ν) (ht : 0 < t) (hx : 0 < x) :
    ∫ y in Ioi 0, conditionedPositiveTransitionDensity ν t x y = 1 := by
  let c := Real.exp (-2 * ν * x)
  have he (y : ℝ) (hy : y ∈ Ioi 0) :
      conditionedPositiveTransitionDensity ν t x y =
        (brownianHeatPair t (x + ν * t) y - c * brownianHeatPair t (x - ν * t) y) /
          conditionedH ν x := by
    let E (v : ℝ) := Real.exp (v * (y - x) - v ^ 2 * t / 2)
    let D := brownianHeatDensity t (y - x) - brownianHeatDensity t (y + x)
    have htilt (v : ℝ) : E v * D = brownianHeatDensity t (y - (x + v * t)) -
        Real.exp (-2 * v * x) * brownianHeatDensity t (y + (x - v * t)) := by
      dsimp [E, D]
      rw [mul_sub, brownianHeatDensity_tilt ht,
        show v * (y - x) - v ^ 2 * t / 2 = -2 * v * x + (v * (y + x) - v ^ 2 * t / 2) by ring,
        Real.exp_add, mul_assoc, brownianHeatDensity_tilt ht]
      ring_nf
    have hE : E ν * Real.exp (-2 * ν * y) = c * E (-ν) := by
      dsimp [E, c]
      simp only [← Real.exp_add]
      congr 1
      ring
    have hc : c * Real.exp (-2 * -ν * x) = 1 := by
      dsimp [c]
      rw [← Real.exp_add, show -2 * ν * x + -2 * -ν * x = 0 by ring, Real.exp_zero]
    rw [conditionedPositiveTransitionDensity, ite_eq_left ⟨hν.le, ht, hx, hy⟩,
      show conditionedH ν y = 1 - Real.exp (-2 * ν * y) by simp [conditionedH, hν.ne']]
    change (E ν * D * (1 - _) : ℝ) / _ = _
    congr 1
    calc
      _ = E ν * D - c * (E (-ν) * D) := by
        rw [mul_sub, mul_one, show E ν * D * Real.exp (-2 * ν * y) =
          (E ν * Real.exp (-2 * ν * y)) * D by ring, hE, mul_assoc]
      _ = _ := by
        rw [htilt ν, htilt (-ν), mul_sub, ← mul_assoc c, hc, one_mul]
        unfold brownianHeatPair c
        ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi he, integral_div,
    integral_sub (integrable_brownianHeatPair ht _).integrableOn
      ((integrable_brownianHeatPair ht _).const_mul c).integrableOn,
    integral_const_mul, integral_brownianHeatPair ht, integral_brownianHeatPair ht, mul_one]
  rw [show 1 - c = conditionedH ν x by simp [c, conditionedH, hν.ne']]
  exact div_self (conditionedH_pos hν.le hx).ne'

end DOZZ.Proofs

end
