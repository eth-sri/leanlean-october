/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Normalized Lebesgue measure on a disk, used for local finite-cutoff chaos integrals. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace DOZZ.Proofs

/-- Normalized volume on the subtype of the closed disk of radius `R`. -/
noncomputable def localBallProbability (R : ℝ) :
    Measure {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R} := by
  let S := {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}
  letI : MeasureSpace S := Measure.Subtype.measureSpace
  exact ((volume : Measure S) Set.univ)⁻¹ • (volume : Measure S)

theorem localBallVolume_univ (R : ℝ) :
    letI := Measure.Subtype.measureSpace (p := fun z => z ∈ Metric.closedBall (0 : ℂ) R)
    (volume : Measure {z : ℂ // z ∈ Metric.closedBall (0 : ℂ) R}) Set.univ =
      ENNReal.ofReal R ^ 2 * (NNReal.pi : ℝ≥0∞) := by
  rw [Measure.Subtype.volume_univ Metric.isClosed_closedBall.measurableSet.nullMeasurableSet,
    Complex.volume_closedBall]
theorem localBallProbability_isProbability {R : ℝ} (hR : 0 < R) :
    IsProbabilityMeasure (localBallProbability R) := by
  refine ⟨?_⟩
  rw [localBallProbability, Measure.smul_apply, smul_eq_mul, localBallVolume_univ]
  exact ENNReal.inv_mul_cancel
    (mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_ne_zero_iff.mpr hR))
      (ENNReal.coe_ne_zero.mpr NNReal.pi_pos.ne')) (by finiteness)

end DOZZ.Proofs
