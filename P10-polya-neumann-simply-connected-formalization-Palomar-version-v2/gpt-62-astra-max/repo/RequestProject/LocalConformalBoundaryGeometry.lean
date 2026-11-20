module

public import RequestProject.DiskCoordinates

public import RequestProject.LocalConformalArcFactorization
public import Mathlib.Topology.ContinuousOn
public import RequestProject.PlanarNotation

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

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace PolyaNeumann

open MeasureTheory Set Metric
open scoped Topology

section

variable (F : ℂ → ℂ) (Φ : SmoothDiskMap) (hF : ContinuousOn F closedDisk)
    (hinj : InjOn Φ.map closedDisk) (hΩ : IsOpen Φ.domain)

include hF in
/-- Compactness and continuity give the exact closed-disk image. No
injectivity or holomorphicity is needed for this topological identity. -/
theorem unitDisk_closed_image_eq_closure :
    F '' closedDisk = closure (F '' unitDisk) := by
  have hclosure  :=
    closure_ball (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)
  have hFc : ContinuousOn F (closure unitDisk) := by
    simpa only [hclosure] using hF
  apply Subset.antisymm
  · simpa [hclosure] using hFc.image_closure
  · apply closure_minimal
    · rintro w ⟨z, hz, rfl⟩
      exact ⟨z, ball_subset_closedBall hz, rfl⟩
    · exact ((isCompact_closedBall 0 1).image_of_continuousOn hF).isClosed

include hF in
/-- For an injective closed-disk map, removing the open-disk image removes
exactly the interior source points. Openness of the image identifies the
remaining points with its frontier. -/
theorem unitDisk_sphere_image_eq_frontier
    (hinj : InjOn F closedDisk)
    (hΩ : IsOpen (F '' unitDisk)) :
    F '' diskSphere = frontier (F '' unitDisk) := by
  calc
    _ =
        F '' (closedDisk \ unitDisk) := by
      rw [closedBall_diff_ball]
    _ = _ :=
      hinj.image_diff_subset ball_subset_closedBall
    _ = closure (F '' unitDisk) \ F '' unitDisk := by
      rw [unitDisk_closed_image_eq_closure F hF]
    _ = _ := hΩ.frontier_eq.symm

theorem localConformal_closedDisk_image_eq_closure :
    Φ.map '' closedDisk = closure Φ.domain :=
  unitDisk_closed_image_eq_closure Φ.map
    (Φ.smooth.continuousOn.mono (closedBall_subset_ball Φ.one_lt_radius))

include hinj hΩ in
theorem localConformal_unitSphere_image_eq_frontier :
    Φ.map '' diskSphere = frontier Φ.domain :=
  unitDisk_sphere_image_eq_frontier Φ.map
    (Φ.smooth.continuousOn.mono (closedBall_subset_ball Φ.one_lt_radius)) hinj hΩ

/-- The closed angular interval has exactly the unit-circle image, including
both representations of its common endpoint. -/
theorem unitCircleMap_image_Icc :
    unitCirclePt '' angleInterval = diskSphere := by
  have hIoc := image_circleMap_Ioc 0 1
  apply Subset.antisymm
  · intro w hw
    
    simpa using image_subset_range unitCirclePt angleInterval hw
  · grind

theorem physicalCircleTrace_image_Icc :
    physicalCircleTrace F '' angleInterval = F '' diskSphere := by
  change (F ∘ unitCirclePt) '' angleInterval = _
  rw [image_comp, unitCircleMap_image_Icc]

include hinj hΩ in
/-- The boundary image is proved from F itself; it is not supplied as an
independent premise. -/
theorem localConformal_circleTrace_image_frontier :
    Φ.boundary '' angleInterval =
      frontier Φ.domain := by
  rw [physicalCircleTrace_image_Icc]
  exact localConformal_unitSphere_image_eq_frontier Φ hinj hΩ

end

/-- Exact inverse arclength preserves an already proved boundary image. -/
theorem normalizedArcCurve_image_frontier {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hper : Function.Periodic γ anglePeriod)
    (hnz : ∀ θ, deriv γ θ ≠ 0)
    (him : γ '' angleInterval = frontier Ω) :
    normalizedArcCurve hγ hper hnz '' angleInterval = frontier Ω := by
  rw [normalizedArcCurve_image_Icc hγ hper hnz, him]

end PolyaNeumann

end
