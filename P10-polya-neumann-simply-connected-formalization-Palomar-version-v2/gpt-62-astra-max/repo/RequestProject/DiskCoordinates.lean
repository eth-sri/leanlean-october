module

public import RequestProject.Defs
public import RequestProject.PlanarNotation
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-! The disk-coordinate data used in the conditional conformal calculations. Each
level adds just the bounds or inverse chart needed for that part of the proof. -/

@[expose] public section

namespace PolyaNeumann

open Set Metric
open scoped ContDiff

structure SmoothDiskMap where
  {radius : ℝ}
  one_lt_radius : 1 < radius
  map : ℂ → ℂ
  smooth : ContDiffOn ℝ ∞ map (ball 0 radius)

structure ConformalDiskMap extends SmoothDiskMap where
  {C : ℝ}
  bounded : Bornology.IsBounded (map '' unitDisk)
  lipschitzDomain : IsLipschitzDomain (map '' unitDisk)
  holomorphic : DifferentiableOn ℂ map unitDisk
  inj : InjOn map unitDisk
  deriv_lower : ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv map z‖ ^ 2

structure ControlledDiskMap extends ConformalDiskMap where
  {K : ℝ}
  deriv_upper : ∀ z ∈ unitDisk, ‖fderiv ℝ map z 1‖ ≤ K

structure DiskCoordinates extends ControlledDiskMap where
  chart : OpenPartialHomeomorph ℂ ℂ
  chart_eq : (chart : ℂ → ℂ) = map
  source : closedDisk ⊆ chart.source
  smoothInverse : ContDiffOn ℝ ∞ chart.symm chart.target

instance : Coe ConformalDiskMap SmoothDiskMap := ⟨ConformalDiskMap.toSmoothDiskMap⟩
instance : Coe ControlledDiskMap ConformalDiskMap := ⟨ControlledDiskMap.toConformalDiskMap⟩
instance : Coe DiskCoordinates ControlledDiskMap := ⟨DiskCoordinates.toControlledDiskMap⟩

/-- The physical domain parametrized by the chart. -/
abbrev SmoothDiskMap.domain (φ : SmoothDiskMap) := φ.map '' unitDisk

/-- The smooth inverse forces the actual closed-disk real differential to
be nonzero, including at the boundary. -/
theorem SmoothDiskMap.closedDifferential_ne_zero (Φ : SmoothDiskMap)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = Φ.map) (hsource : closedDisk ⊆ e.source)
    (hes : ContDiffOn ℝ ∞ e.symm e.target) :
    ∀ z ∈ closedDisk, fderiv ℝ Φ.map z 1 ≠ 0 := by
  rw [← he]
  intro z hz hzero
  have hdF := (Φ.smooth.contDiffAt (isOpen_ball.mem_nhds (closedBall_subset_ball Φ.one_lt_radius hz))).differentiableAt (by simp)
  rw [← he] at hdF
  have hdG := (hes.contDiffAt (e.open_target.mem_nhds (e.mapsTo (hsource hz)))).differentiableAt (by simp)
  have h := ((hdG.hasFDerivAt.comp z hdF.hasFDerivAt).congr_of_eventuallyEq
    ((e.eventually_left_inverse (hsource hz)).mono fun _ h => h.symm)).unique (hasFDerivAt_id z)
  simpa [hzero] using congrArg (fun A : ℂ →L[ℝ] ℂ => A 1) h

end PolyaNeumann
