/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Surface.ResidueCover
import CCDN.Surface.PrimeWindowSubpower
import Mathlib.Algebra.Order.Star.Real

/-! A degree-dependent logarithmic prime window discharges all height
conditions of the surface residue cover. Its complete residual point count
is O(B), uniformly in coefficients, auxiliaries and initial curve families. -/

namespace CCDN
noncomputable section

section
variable (d : ℕ)

/-- The constant `4 log (d + 1) + K + d + 2` scaling the logarithmic prime window of the residue
cover for a surface of degree `d` with logarithmic height constant `K`. -/
def surfaceResidueWindowScale (K : ℝ) : ℝ :=
  4 * Real.log ((d : ℝ) + 1) + K + d + 2

/-- The logarithmic size `surfaceResidueWindowScale d K * (log B + 1)` of the prime window of
the residue cover for a surface of degree `d` in the box of radius `B`. -/
def surfaceResidueWindow (K B : ℝ) : ℝ :=
  surfaceResidueWindowScale d K * (Real.log B + 1)

/-- The constant `1 + (log 4 + 4) c s`, with `c` the constant `scalingPrimeRatio` and `s` the
window scale `surfaceResidueWindowScale d K`, by which the logarithmic budget of the residue
cover is a multiple of `log B + 1`. -/
def surfaceResidueLogScale (K : ℝ) : ℝ :=
  1 + (Real.log 4 + 4) * scalingPrimeRatio * surfaceResidueWindowScale d K

/-- For `K ≥ 0`, the window scale `surfaceResidueWindowScale d K` is at least two. -/
theorem surfaceResidueWindowScale_two_le {K : ℝ} (hK : 0 ≤ K) :
    2 ≤ surfaceResidueWindowScale d K := by
  have hh := Real.log_nonneg (show (1 : ℝ) ≤ d + 1 by grind)
  unfold surfaceResidueWindowScale
  nlinarith

/-- For `K ≥ 0` and `B ≥ 1`, the prime window size `surfaceResidueWindow d K B` is at
least one. -/
theorem surfaceResidueWindow_one_le {K B : ℝ} (hK : 0 ≤ K) (hB : 1 ≤ B) :
    1 ≤ surfaceResidueWindow d K B := by
  have hscale := surfaceResidueWindowScale_two_le d hK
  have hlog := Real.log_nonneg hB
  unfold surfaceResidueWindow
  nlinarith

/-- For the prime window `surfaceResidueWindow d K B`, the logarithmic budget of the residue
cover equals `surfaceResidueLogScale d K * (log B + 1)`. -/
theorem surfaceResidueLogBudget_window (K B : ℝ) :
    surfaceResidueLogBudget B (surfaceResidueWindow d K B) =
      surfaceResidueLogScale d K * (Real.log B + 1) := by
  unfold surfaceResidueLogBudget surfaceResidueWindow surfaceResidueLogScale
  ring

end

section
variable {K B H : ℝ}

/-- The chosen window meets both the derivative-height condition and the
terminal-modulus threshold, even at B = 1. -/
theorem surfaceResidueWindow_parameters {d : ℕ} (hd : 1 ≤ d)
    (hK : 0 ≤ K) (hB : 1 ≤ B)
    (hheight : Real.log H ≤ K * (Real.log B + 1)) :
    4 * Real.log ((d : ℝ) + 1) + Real.log H + d * Real.log B ≤
        surfaceResidueWindow d K B ∧
      1 < 2 * B ^ (1 / Real.sqrt (d : ℝ)) ∧
      B ^ (1 / Real.sqrt (d : ℝ)) ≤ 2 * B ^ (1 / Real.sqrt (d : ℝ)) ∧
      2 * B ^ (1 / Real.sqrt (d : ℝ)) ≤ Real.exp (surfaceResidueWindow d K B) := by
  have hB0 := zero_lt_one.trans_le hB
  have hlogB := Real.log_nonneg hB
  have hlogd := Real.log_nonneg (show (1 : ℝ) ≤ d + 1 by grind)
  have hdR : (1 : ℝ) ≤ d := mod_cast hd
  have hsqrt : 1 ≤ Real.sqrt d := Real.le_sqrt_of_sq_le (by grind)
  have hroot : 0 ≤ 1 / Real.sqrt d := by positivity
  have hroot1 : 1 / Real.sqrt d ≤ 1 := by bound
  have hp := Real.one_le_rpow hB hroot
  refine ⟨?_, by linarith, by linarith, ?_⟩
  · unfold surfaceResidueWindow surfaceResidueWindowScale
    nlinarith
  · have hlog2 : Real.log 2 ≤ (2 : ℝ) := Real.log_le_self (by norm_num)
    have hscale := surfaceResidueWindowScale_two_le d hK
    have hlogX : Real.log (2 * B ^ (1 / Real.sqrt d)) ≤
        surfaceResidueWindow d K B := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hB0]
      unfold surfaceResidueWindow
      have hh := mul_le_mul_of_nonneg_right hroot1 hlogB
      nlinarith
    have hh := Real.exp_le_exp.mpr hlogX
    rwa [Real.exp_log (by positivity)] at hh

/-- For a surface equation of degree `d ≥ 1` whose coefficients are bounded by `H ≥ 1` with
`log H ≤ K (log B + 1)`, the chosen window `surfaceResidueWindow d K B` and the cutoff
`2 B^(1/√d)` are residue-cover parameters. -/
theorem isSurfaceResidueWindow_of_log_height {f : MvPolynomial (Fin 3) ℤ}
    (hd : 1 ≤ f.totalDegree) (hK : 0 ≤ K) (hB : 1 ≤ B) (hH : 1 ≤ H)
    (hcoeff : CoefficientHeightLE f H) (hheight : Real.log H ≤ K * (Real.log B + 1)) :
    IsSurfaceResidueWindow f B H (surfaceResidueWindow f.totalDegree K B)
      (2 * B ^ (1 / Real.sqrt (f.totalDegree : ℝ))) := by
  obtain ⟨hderivative, hX, hBX, hXL⟩ := surfaceResidueWindow_parameters hd hK hB hheight
  exact ⟨hB, hH, surfaceResidueWindow_one_le _ hK hB, hcoeff, hderivative, hX, hBX, hXL⟩

end

