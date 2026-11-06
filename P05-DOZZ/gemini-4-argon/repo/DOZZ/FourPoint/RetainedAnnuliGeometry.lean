/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.FourPoint.RetainedAnnuliAllocation

/-! Uniform retained disks for the local freezing estimate. -/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DOZZ.Proofs


/-- Distances to the center on a retained disk vary by less than its radius. -/
theorem retained_disk_radial_bounds z (s ρ : ℝ) (hs : 0 ≤ s)
    x (hx : x ∈ Metric.ball (z + (s : ℂ)) ρ) :
    s - ρ < ‖x - z‖ ∧ ‖x - z‖ < s + ρ := by
  have real_displacement_norm : ‖(z + (s : ℂ)) - z‖ = s := by
    rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have hx' : ‖x - (z + (s : ℂ))‖ < ρ := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  have hu := real_displacement_norm
  have hupper := norm_add_le (x - (z + (s : ℂ))) ((z + (s : ℂ)) - z)
  have hlower := norm_add_le ((z + (s : ℂ)) - x) (x - z)
  rw [(show x - (z + (s : ℂ)) + ((z + (s : ℂ)) - z) = x - z by abel), hu] at hupper
  rw [(show (z + (s : ℂ)) - x + (x - z) = (z + (s : ℂ)) - z by abel), hu, norm_sub_rev (z + (s : ℂ)) x] at hlower
  exact ⟨by linarith only [hlower, hx'], by linarith only [hupper, hx']⟩

/-- The small freezing disk lies on the scale `ε` and inside the literal outer annulus. -/
theorem freezing_inner_disk z (ε t R : ℝ)
    (hε : 0 < ε) (hεt : ε < t / 32) (htR : t ≤ R / 2) :
    Metric.ball (z + ((3 * ε : ℝ) : ℂ)) (ε / 2) ⊆
      {x | ε < ‖x - z‖ ∧ ‖x - z‖ < R} := by
  intro x hx
  obtain ⟨hl, hu⟩ := retained_disk_radial_bounds z (3 * ε) (ε / 2)
    (by positivity) x hx
  constructor <;> linarith only [hε, hεt, htR, hl, hu]

/-- The fixed freezing disk lies away from the root and inside the same annulus. -/
theorem freezing_outer_disk z (ε t R : ℝ)
    (hε : 0 < ε) (hεt : ε < t / 32) (htR : t ≤ R / 2) :
    Metric.ball (z + (t : ℂ)) (t / 8) ⊆
      {x | ε < ‖x - z‖ ∧ ‖x - z‖ < R} := by
  intro x hx
  obtain ⟨hl, hu⟩ := retained_disk_radial_bounds z t (t / 8) (show 0 < t by linarith only [hε, hεt]).le x hx
  constructor <;> linarith only [hε, hεt, htR, hl, hu]

/-- The two retained disks have a fixed positive spatial gap. -/
theorem freezing_disk_separation z (ε t : ℝ)
    (hε : 0 < ε) (hεt : ε < t / 32) :
    ε / 2 + t / 8 + t / 2 ≤ ‖(z + ((3 * ε : ℝ) : ℂ)) - (z + (t : ℂ))‖ := by
  rw [(show (z + ((3 * ε : ℝ) : ℂ)) - (z + (t : ℂ)) = ((3 * ε - t : ℝ) : ℂ) by push_cast; abel), Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith only [hε, hεt])]
  linarith only [hε, hεt]

end DOZZ.Proofs
