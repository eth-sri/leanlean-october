/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SpatialBoundary
public import DOZZ.FourPoint.Reflected.SourceFullComparison
import Mathlib.Tactic
/-! Literal separated inner and outer regions for conditional lateral comparison. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace DOZZ.Proofs

/-- The inner region excludes the radial singularity. -/
def reflected_innerRegion (s : ℝ) : Set ℂ := {x | 0 < ‖x‖ ∧ ‖x‖ < s}
/-- The exterior excludes the fixed insertion roots. -/
def reflected_outerRegion (r : ℝ) : Set ℂ := {x | r < ‖x‖} ∩ ({0, 1} : Set ℂ)ᶜ

/-- Every geometric hypothesis of the full comparison holds on these literal regions. -/
theorem reflected_separated_region_geometry (s r : ℝ) (_hs : 0 < s) (hr : 0 < r)
    (hr1 : r ≤ 1) (hsep : s/r ≤ 1/2) :
    IsOpen (reflected_innerRegion s) ∧ IsOpen (reflected_outerRegion r) ∧
    reflected_innerRegion s ⊆ ({0, 1} : Set ℂ)ᶜ ∧
    reflected_outerRegion r ⊆ ({0, 1} : Set ℂ)ᶜ ∧
    reflected_innerRegion s ⊆ Metric.ball 0 r ∧
    reflected_outerRegion r ⊆ (Metric.ball 0 r)ᶜ ∧
    (∀ x ∈ reflected_innerRegion s, ‖x‖ ≤ (s/r)*r) ∧
    (∀ x ∈ reflected_outerRegion r, r ≤ ‖x‖) ∧
    Metric.closedBall (3 : ℂ) (1/8) ⊆ reflected_outerRegion r := by
  have hsr : s ≤ r/2 := by
    have h := (div_le_iff₀ hr).mp hsep
    linarith only [h]
  have hs1 : s < 1 := by linarith only [hsr, hr1]
  refine ⟨?_, ?_, ?_, inter_subset_right, ?_, ?_, ?_, ?_, ?_⟩
  · exact (isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)
  · exact (isOpen_lt continuous_const continuous_norm).inter
      (isClosed_singleton.union isClosed_singleton).isOpen_compl
  · intro x hx
    have hx1 : x ≠ 1 := by
      intro hh
      have h := hx.2
      simp only [hh, norm_one] at h
      exact (not_lt_of_ge hs1.le) h
    simp [(norm_pos_iff.mp hx.1), hx1]
  · intro x hx
    simpa only [Metric.mem_ball, dist_zero_right] using hx.2.trans_le (by linarith only [hsr, hr])
  · intro x hx hh
    have hn : ‖x‖ < r := by simpa only [Metric.mem_ball, dist_zero_right] using hh
    exact (not_lt_of_ge hx.1.le) hn
  · intro x hx
    rw [div_mul_cancel₀ s hr.ne']
    exact hx.2.le
  · exact fun x hx => hx.1.le
  · intro x hx
    have hd : ‖x-(3 : ℂ)‖ ≤ 1/8 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    have hn := norm_sub_norm_le (3 : ℂ) x
    rw [norm_sub_rev] at hn
    have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
    rw [h3] at hn
    have hxnorm : 1 < ‖x‖ := by linarith only [hn, hd]
    refine ⟨hr1.trans_lt hxnorm, ?_⟩
    have hx1 : x ≠ 1 := by intro hh; simp [hh] at hxnorm
    simp [(norm_pos_iff.mp (zero_lt_one.trans hxnorm)), hx1]

end DOZZ.Proofs
