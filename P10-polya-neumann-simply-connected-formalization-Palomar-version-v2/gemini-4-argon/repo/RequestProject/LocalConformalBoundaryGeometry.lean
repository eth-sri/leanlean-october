module

public import RequestProject.LocalConformalArcFactorization
public import Mathlib.Topology.ContinuousOn

/-!
# Boundary geometry of actual supplied disk coordinates

Continuity on the closed unit disk identifies its compact image with the
closure of the open-disk image. Closed-disk injectivity then identifies the
image of the unit sphere with the frontier whenever the open-disk image is
open. These are consequences of the supplied map, rather than additional
boundary-image assumptions.

The actual circle trace and its exact inverse-arclength curve therefore have
the physical boundary image. The final theorem constructs all five
orientation-free fields of a boundary parametrization, together with the
precise normalized arclength factorization and its C1 witness. The signed-area
field of `IsBoundaryParam` still requires a proof of positive orientation.
Existence of the initial supplied conformal map is a separate obligation.
-/

@[expose] public section


noncomputable section

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology ContDiff

/-- Compactness and continuity give the exact closed-disk image. No
injectivity or holomorphicity is needed for this topological identity. -/
theorem unitDisk_closed_image_eq_closure (F : ℂ → ℂ)
    (hF : ContinuousOn F (closedBall 0 1)) :
    F '' closedBall 0 1 = closure (F '' ball 0 1) := by
  have hclosure :=
    closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)
  apply Subset.antisymm
  · simpa [hclosure] using (show ContinuousOn F (closure (ball (0 : ℂ) 1)) by
      simpa [hclosure] using hF).image_closure
  · apply closure_minimal
    · rintro w ⟨z, hz, rfl⟩
      exact ⟨z, ball_subset_closedBall hz, rfl⟩
    · exact ((isCompact_closedBall 0 1).image_of_continuousOn hF).isClosed

theorem localConformal_closedDisk_image_eq_closure  (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ ∞ F (ball 0 R)) :
    F '' closedBall 0 1 = closure (F '' ball 0 1) :=
  unitDisk_closed_image_eq_closure F
    (hFs.continuousOn.mono (closedBall_subset_ball hR))

theorem physicalCircleTrace_image_Icc F :
    physicalCircleTrace F '' Icc 0 (2 * Real.pi) = F '' sphere 0 1 := by
  change (F ∘ circleMap 0 1) '' Icc 0 (2 * Real.pi) = _
  rw [image_comp, show circleMap 0 1 '' Icc 0 (2 * Real.pi) = sphere 0 1 by
    apply Subset.antisymm
    · intro w hw
      simpa using image_subset_range (circleMap 0 1) (Icc 0 (2 * Real.pi)) hw
    · rw [← (show circleMap 0 1 '' Ioc 0 (2 * Real.pi) = sphere 0 1 by
        simp)]
      rintro w ⟨θ, hθ, rfl⟩
      exact ⟨θ, ⟨hθ.1.le, hθ.2⟩, rfl⟩]

/-- The boundary image is proved from F itself; it is not supplied as an
independent premise. -/
theorem localConformal_circleTrace_image_frontier  (hR : 1 < R)
    (F : ℂ → ℂ) (hFs : ContDiffOn ℝ ∞ F (ball 0 R))
    (hinj : InjOn F (closedBall 0 1))
    (hΩ : IsOpen (F '' ball 0 1)) :
    physicalCircleTrace F '' Icc 0 (2 * Real.pi) =
      frontier (F '' ball 0 1) := by
  rw [physicalCircleTrace_image_Icc]
  exact (by
    calc
      _ = _ := by
        rw [closedBall_diff_ball]
      _ = _ :=
        hinj.image_diff_subset ball_subset_closedBall
      _ = _ := by
        rw [unitDisk_closed_image_eq_closure F (hFs.continuousOn.mono (closedBall_subset_ball hR))]
      _ = _ := hΩ.frontier_eq.symm)

/-- Exact inverse arclength preserves an already proved boundary image. -/
theorem normalizedArcCurve_image_frontier {Ω : Set ℂ} 
    (hγ : ContDiff ℝ 1 γ) hper
    hnz
    (him : γ '' Icc 0 (2 * Real.pi) = frontier Ω) :
    normalizedArcCurve hγ hper hnz '' Icc 0 (2 * Real.pi) = frontier Ω := by
  rw [normalizedArcCurve_image_Icc hγ hper hnz, him]

end PolyaNeumann

end
