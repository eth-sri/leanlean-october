/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Correlations.Tails.PinEnvelopeMoment
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! Finite moments of the complete first-order copied-multiplier envelope. -/

@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- The first-order coefficient is absorbed by a pure exponential of the pin correction. -/
theorem polynomial_pin_envelope_le (D d s : ℝ)
    (hD : 0 ≤ D) (hd : 0 ≤ d) (hs : 0 ≤ s) :
    (d+s*(D+4))*Real.exp (D+4) ≤
      ((d+5*s)*Real.exp 4)*Real.exp (2*D) := by
  have he : 1 ≤ Real.exp D := Real.one_le_exp hD
  have hDe : D ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hc : d+s*(D+4) ≤ (d+5*s)*Real.exp D := by
    have h1 := mul_le_mul_of_nonneg_left he hd
    have h2 := mul_le_mul_of_nonneg_left hDe hs
    have h3 := mul_le_mul_of_nonneg_left he (show 0 ≤ 4*s by positivity)
    nlinarith only [h1,h2,h3]
  calc
    _ ≤ ((d+5*s)*Real.exp D)*Real.exp (D+4) :=
      mul_le_mul_of_nonneg_right hc (Real.exp_nonneg _)
    _ = _ := by
      simp_rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

end DOZZ.Proofs
