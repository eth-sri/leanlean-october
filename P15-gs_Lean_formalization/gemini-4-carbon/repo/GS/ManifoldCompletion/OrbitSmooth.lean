module

public import GS.ManifoldCompletion.OrbitAtlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import GS.Continuation.AmbientProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Smooth inclusion and intrinsic use of the point-only projection formula

The first result uses the constructed atlas on the actual orbit. It is not merely
smoothness with respect to factor parameters. The projector is inherited from
the checked Continuation module. Identifying its range with the image of the
manifold tangent bundle is proved separately in TangentBridge.lean.

-/

noncomputable section
set_option maxHeartbeats 800000
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Continuation Filter Set
open scoped Topology Manifold
namespace GS.ManifoldCompletion
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n))
variable [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)]

end GS.ManifoldCompletion
