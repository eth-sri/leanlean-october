module

public import GS.UnitarySharing.BundleRetraction
public import GS.UnitarySharing.Gradient
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Intrinsic shared descent through the canonical whole-bundle retraction

The curve is the exact point-and-tangent Cayley map. Its negative intrinsic
gradient has loss derivative minus the squared induced Frobenius norm.
Armijo steps exist and geometric backtracking terminates for a nonzero
gradient. These are actual shared-orbit statements for any fixed carrier.
No convergence rate or floating-point implementation theorem is asserted.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.RiemannianCompletion Filter
open scoped Topology Manifold
namespace GS.UnitarySharing
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (right left : Pattern n) (P : CMat n)
local instance descentNormedSpace : NormedSpace ℝ (HorizontalModel right left P) :=
  Submodule.normedSpace _
local instance descentChartedSpace : ChartedSpace (HorizontalModel right left P)
    (MatrixOrbit right left P) := sharedOrbitChartedSpace right left P
local instance descentIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

end GS.UnitarySharing
