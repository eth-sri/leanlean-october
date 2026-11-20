module

public import RequestProject.ConformalDiskCoordinates
public import RequestProject.RiemannMappingInterior
public import RequestProject.PhysicalHardySupport
public import Mathlib.Analysis.Complex.RemovableSingularity

@[expose] public section

noncomputable section

namespace PolyaNeumann

open Set Metric Complex
open scoped Real

lemma ConformalDiskCoordinates.trace_contDiff {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F) :
    ContDiff ℝ 1 (physicalCircleTrace F) :=
  contDiff_physicalCircleTrace_of_neighborhood coords.one_lt_radius F (coords.smooth.of_le (by simp))

lemma ConformalDiskCoordinates.trace_deriv {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F) (t : ℝ) :
    deriv (physicalCircleTrace F) t = deriv F (circleMap 0 1 t) * (circleMap 0 1 t * I) :=
  ((coords.differentiableAt_closed (circleMap_mem_closedBall 0 zero_le_one t)).hasDerivAt.comp t
    (hasDerivAt_circleMap 0 1 t)).deriv

lemma ConformalDiskCoordinates.trace_deriv_ne_zero {F : ℂ → ℂ} (coords : ConformalDiskCoordinates F)
    (t : ℝ) : deriv (physicalCircleTrace F) t ≠ 0 := by
  rw [coords.trace_deriv]
  simp [coords.deriv_ne_zero_closed (circleMap_mem_closedBall _ zero_le_one t)]

/-- Cauchy's formula after pulling back the simple pole by a holomorphic chart. -/
lemma circle_pullback_pole {F g : ℂ → ℂ} {r : ℝ} {x : ℂ} (hx : x ∈ ball 0 r)
    (hF : DifferentiableOn ℂ F (closedBall 0 r)) (hi : InjOn F (closedBall 0 r))
    (hn : deriv F x ≠ 0) (hg : DifferentiableOn ℂ g (closedBall 0 r)) :
    (∮ z in C(0, r), g z / (F z - F x)) = (2 * π * I) * (g x / deriv F x) := by
  have hds := (Complex.differentiableOn_dslope (closedBall_mem_nhds_of_mem hx)).mpr hF
  have hd0 (z : ℂ) (hz : z ∈ closedBall 0 r) : dslope F x z ≠ 0 := by
    by_cases h : z = x
    · simpa [h, dslope_same] using hn
    · rw [dslope_of_ne F h, slope]
      exact smul_ne_zero (inv_ne_zero (sub_ne_zero.mpr h))
        (sub_ne_zero.mpr (fun h' => h (hi hz (ball_subset_closedBall hx) h')))
  have h := (hg.div hds hd0).circleIntegral_sub_inv_smul hx
  change (∮ z in C(0, r), (z - x)⁻¹ * (g z / dslope F x z)) =
    (2 * π * I) * (g x / dslope F x x) at h
  rw [dslope_same] at h
  rw [← h]
  apply circleIntegral.integral_congr (pos_of_mem_ball hx).le
  intro z hz
  have hzx : z ≠ x := by
    rintro rfl
    exact (ne_of_lt (mem_ball.mp hx)) (mem_sphere.mp hz)
  change g z / (F z - F x) = (z - x)⁻¹ * (g z / dslope F x z)
  rw [dslope_of_ne F hzx, slope, smul_eq_mul, vsub_eq_sub]
  field_simp [sub_ne_zero.mpr hzx, sub_ne_zero.mpr fun h => hzx (hi (sphere_subset_closedBall hz)
    (ball_subset_closedBall hx) h)]

end PolyaNeumann
