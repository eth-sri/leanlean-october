module

public import Mathlib.Analysis.Complex.RealDeriv

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import RequestProject.CirclePeriod

/-! Common notation for the unit disk, its circle map, and the boundary parameter intervals.
Notation keeps these geometric descriptions identical when rewriting interval and ball formulas. -/

@[expose] public section

namespace PolyaNeumann

scoped notation "unitDisk" => Metric.ball (0 : ℂ) 1
scoped notation "closedUnitDisk" => Metric.closedBall (0 : ℂ) 1
scoped notation "unitCircleMap" => circleMap (0 : ℂ) 1
scoped notation "boundaryInterval" => Set.Icc (0 : ℝ) (2 * Real.pi)
scoped notation "boundaryHalfOpenInterval" => Set.Ioc (0 : ℝ) (2 * Real.pi)

/- The standard lower-Jacobian and upper-differential bounds for a disk chart. -/
set_option quotPrecheck false

scoped notation "DiskInverseJacobianBound" F:arg C:arg =>
  ∀ z ∈ unitDisk, 1 ≤ C * ‖deriv F z‖ ^ 2
scoped notation "DiskDerivativeBound" F:arg K:arg =>
  ∀ z ∈ unitDisk, ‖fderiv ℝ F z 1‖ ≤ K

end PolyaNeumann
