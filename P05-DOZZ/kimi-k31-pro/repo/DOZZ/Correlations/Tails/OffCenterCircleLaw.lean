/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import DOZZ.Correlations.Tails.OffCenterLateralLaw
import DOZZ.Statements.GFFStructure.CircleAverageCovariance

/-! Exact local circle law after removing the off-center Gaussian origin.
The circle must stay in the translated unit disk; intersecting pairs of circles
are allowed, since the full circle potential `DOZZ.circleLogPotential` is retained. -/


open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace DOZZ.Proofs

/-- Circle coordinates whose closed circle lies in the unit disk. -/
abbrev localCircle := {p : ℂ × ℝ // ‖p.1‖ + Real.exp (-p.2) ≤ 1}

/-- Exterior pin potential for a circle, including a circle tangent to the equator. -/
theorem circle_pin_exterior (w : ℂ) (r : ℝ)
    (hw : Real.exp (-r) + 1 ≤ ‖w‖) :
    circleLogPotential ‖w‖₊ ⟨Real.exp (-r), Real.exp_pos _⟩ ⟨1, by norm_num⟩ =
      Real.log ‖w‖ :=
  circleLogPotential_of_radii_le_distance _ _ hw

/-- Translated admissible circles stay outside the equator at an allowed insertion center. -/
theorem localCircle_exterior (z : ℂ) (hz : 2 ≤ ‖z‖) (p : localCircle) :
    Real.exp (-p.val.2) + 1 ≤ ‖z + p.val.1‖ := by
  have h := norm_sub_norm_le z (z + p.val.1)
  simp [sub_add_cancel_left, norm_neg] at h
  linarith [p.property]

/-- Removing the same Gaussian origin from all translated circles cancels both pin terms. -/
theorem offCenter_unpinned_circle_covariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (z : ℂ) (hz : 2 ≤ ‖z‖) (p q : localCircle) :
    covariance (fun ω => Xc ω (z + p.val.1) p.val.2 - Xc ω z 0)
      (fun ω => Xc ω (z + q.val.1) q.val.2 - Xc ω z 0) P =
        -circleLogPotential ‖p.val.1 - q.val.1‖₊
          ⟨Real.exp (-p.val.2), Real.exp_pos _⟩
          ⟨Real.exp (-q.val.2), Real.exp_pos _⟩ := by
  let : IsProbabilityMeasure P := hX.1
  have hp := circle_pin_exterior (z + p.val.1) p.val.2
    (localCircle_exterior z hz p)
  have hq := circle_pin_exterior (z + q.val.1) q.val.2
    (localCircle_exterior z hz q)
  have hzpin := circle_pin_exterior z 0 (by simpa [neg_zero, Real.exp_zero, one_add_one_eq_two] using hz)
  have hp0 : circleLogPotential ‖p.val.1‖₊
      ⟨Real.exp (-p.val.2), Real.exp_pos _⟩ ⟨1, by norm_num⟩ = 0 := by
    simpa [Real.log_one] using circleLogPotential_of_add_le (d := ‖p.val.1‖₊)
      ⟨Real.exp (-p.val.2), Real.exp_pos _⟩ ⟨1, by norm_num⟩ p.property
  have hq0 : circleLogPotential ‖q.val.1‖₊
      ⟨Real.exp (-q.val.2), Real.exp_pos _⟩ ⟨1, by norm_num⟩ = 0 := by
    simpa [Real.log_one] using circleLogPotential_of_add_le (d := ‖q.val.1‖₊)
      ⟨Real.exp (-q.val.2), Real.exp_pos _⟩ ⟨1, by norm_num⟩ q.property
  rw [covariance_fun_sub_fun_sub (hc.2.1 _ _) (hc.2.1 _ _) (hc.2.1 _ _) (hc.2.1 _ _)]
  rw [covariance_comm (fun ω => Xc ω z 0)
    (fun ω => Xc ω (z + q.val.1) q.val.2)]
  simp [neg_zero, Real.exp_zero] at hzpin
  rw [circleAverage_covariance P X Xc hX hc,
    circleAverage_covariance P X Xc hX hc (z + p.val.1) z,
    circleAverage_covariance P X Xc hX hc (z + q.val.1) z,
    offCenter_origin_variance X Xc hX hc z hz]
  simp [add_sub_add_left_eq_sub, add_sub_cancel_left,
    neg_zero, Real.exp_zero, hp, hq, hzpin, hp0, hq0]
  ring

/-- The common covariance gives the logarithmic cutoff time as the local variance. -/
theorem local_circle_self_potential (p : localCircle) :
    -circleLogPotential ‖p.val.1 - p.val.1‖₊
      ⟨Real.exp (-p.val.2), Real.exp_pos _⟩
      ⟨Real.exp (-p.val.2), Real.exp_pos _⟩ = p.val.2 := by
  simp [sub_self, nnnorm_zero, circleLogPotential_zero, max_self, Real.log_exp,
    neg_neg]

end DOZZ.Proofs
