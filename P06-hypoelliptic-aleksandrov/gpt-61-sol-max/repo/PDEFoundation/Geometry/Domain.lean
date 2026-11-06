module

public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.Affine
public import Mathlib.Basic.Real.Pointwise
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Quantitative domain predicates

The compatibility boundedness predicate is retained alongside an explicit
Euclidean-diameter bound for quantitative Sobolev estimates.
-/

@[expose] public section

open scoped Pointwise

namespace PDE

/-- Coordinatewise boundedness, compatible with the existing LIH API. -/
def IsBoundedDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R

variable {d : ℕ} (U : Set (Vec d))

/-- The minimal measurable bounded domain class used by Sobolev integration. -/
def IsSobolevRegularDomain  : Prop :=
  MeasurableSet U ∧ IsBoundedDomain U

/-- Every pair of points in `U` is at Euclidean distance at most `D`. -/
def HasEuclideanDiameterLE  (D : ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ U → ∀ ⦃y⦄, y ∈ U →
    vecEuclideanNorm (x - y) ≤ D

namespace IsSobolevRegularDomain

variable {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U)

include hU
theorem measurableSet  :
    MeasurableSet U :=
  hU.1

theorem isBoundedDomain  :
    IsBoundedDomain U :=
  hU.2

end IsSobolevRegularDomain

namespace HasEuclideanDiameterLE

variable {d : ℕ}



variable {U : Set (Vec d)} {D : ℝ} (hU : HasEuclideanDiameterLE U D)

include hU




end HasEuclideanDiameterLE

end PDE
