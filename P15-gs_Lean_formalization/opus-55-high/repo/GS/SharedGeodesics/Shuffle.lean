module

public import GS.SharedGeodesics.Orthogonal
public import GS.Geodesics.ShuffleCondition

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The original scalar-shuffle condition with actual within-layer sharing

The ambient dimension is n = k₁ * right.size; both physical block sizes divide
n by construction of Pattern. The inequality left.size ≤ k₁ is sufficient for
the concrete scalar shuffle, not for an arbitrary permutation.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.SharedGeometry
open scoped Topology Manifold
namespace GS.SharedGeodesics
variable {n : ℕ} (right left : Pattern n) (k₁ : ℕ) (hN : n = k₁ * right.size)
local notation "σ" => GS.Geodesics.scalarShuffleOfSize hN
local instance shuffleNormedSpace : NormedSpace ℝ (HorizontalModel right left (permMatrix σ)) := Submodule.normedSpace _
local instance shuffleChartedSpace : ChartedSpace (HorizontalModel right left (permMatrix σ))
    (MatrixOrbit right left (permMatrix σ)) := sharedOrbitChartedSpace right left (permMatrix σ)
local instance shuffleIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left (permMatrix σ))) ⊤
    (MatrixOrbit right left (permMatrix σ)) := sharedOrbitIsManifold right left (permMatrix σ)

end GS.SharedGeodesics
