module

public import RequestProject.PlanarTypes

public import RequestProject.PlanarGeometry

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

public section

open scoped ContDiff



namespace PolyaNeumann

open MeasureTheory Set Metric

section
variable (F : PlaneMap) (hF : ContinuousOn F closedUnitDisk)
include F hF

/-- Compactness and continuity give the exact closed-disk image. No
injectivity or holomorphicity is needed for this topological identity. -/
theorem unitDisk_closed_image_eq_closure :
    F '' closedUnitDisk = closure (F '' unitDisk) := by
  have hclosure  :=
    closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)
  have hFc : ContinuousOn F (closure unitDisk) := by
    simpa  [hclosure] using hF
  apply Subset.antisymm
  · simpa  [hclosure] using hFc.image_closure
  · apply closure_minimal
    · rintro w ⟨z, hz, rfl⟩
      exact ⟨z, ball_subset_closedBall hz, rfl⟩
    · exact ((isCompact_closedBall 0 1).image_of_continuousOn hF).isClosed

/-- For an injective closed-disk map, removing the open-disk image removes
exactly the interior source points. Openness of the image identifies the
remaining points with its frontier. -/
theorem unitDisk_sphere_image_eq_frontier
    (hinj : InjOn F closedUnitDisk)
    (hΩ : IsOpen (F '' unitDisk)) :
    F '' sphere (0 : ℂ) 1 = frontier (F '' unitDisk) := by
  calc
    F '' sphere 0 1 =
        F '' (closedBall 0 1 \ ball 0 1) := by
      rw [closedBall_diff_ball]
    _ = F '' closedBall 0 1 \ F '' ball 0 1 :=
      hinj.image_diff_subset ball_subset_closedBall
    _ = closure (F '' ball 0 1) \ F '' ball 0 1 := by
      simp_all [unitDisk_closed_image_eq_closure]
    _ = frontier (F '' ball 0 1) := hΩ.frontier_eq.symm

end


section
variable {R } (hR : 1 < R) (F : PlaneMap) (hFs : RealSmoothOnBall F R)

section
include R hR F hFs

theorem localConformal_closedDisk_image_eq_closure :
    F '' closedUnitDisk = closure (F '' unitDisk) :=
  unitDisk_closed_image_eq_closure F
    (hFs.continuousOn.mono (closedBall_subset_ball hR))

theorem localConformal_unitSphere_image_eq_frontier
    (hinj : InjOn F closedUnitDisk)
    (hΩ : IsOpen (F '' unitDisk)) :
    F '' sphere (0 : ℂ) 1 = frontier (F '' unitDisk) :=
  unitDisk_sphere_image_eq_frontier F
    (hFs.continuousOn.mono (closedBall_subset_ball hR)) hinj hΩ

end


/-- The closed angular interval has exactly the unit-circle image, including
both representations of its common endpoint. -/
theorem unitCircleMap_image_Icc :
    unitCircleMap '' boundaryInterval = sphere (0 : ℂ) 1 := by
  have hIoc : unitCircleMap '' boundaryHalfOpenInterval = sphere (0 : ℂ) 1 := by
    norm_num
  apply Subset.antisymm
  · intro w hw
    aesop
  · rw [← hIoc]
    rintro w ⟨θ, hθ, rfl⟩
    grind

theorem physicalCircleTrace_image_Icc F :
    physicalCircleTrace F '' boundaryInterval = F '' sphere (0 : ℂ) 1 := by
  grind [unitCircleMap_image_Icc, PolyaNeumann.physicalCircleTrace]

include R hR F hFs in
/-- The boundary image is proved from F itself; it is not supplied as an
independent premise. -/
theorem localConformal_circleTrace_image_frontier
    (hinj : InjOn F closedUnitDisk)
    (hΩ : IsOpen (F '' unitDisk)) :
    physicalCircleTrace F '' boundaryInterval =
      frontier (F '' unitDisk) := by
  grind only [physicalCircleTrace_image_Icc, localConformal_unitSphere_image_eq_frontier]

end


/-- Exact inverse arclength preserves an already proved boundary image. -/
theorem normalizedArcCurve_image_frontier  
    hγ hper
    (hnz : ∀ θ, deriv γ θ ≠ 0)
    (him : γ '' boundaryInterval = frontier Ω) :
    normalizedArcCurve hγ hper hnz '' boundaryInterval = frontier Ω := by
  rw [normalizedArcCurve_image_Icc hγ hper hnz, him]

end PolyaNeumann
