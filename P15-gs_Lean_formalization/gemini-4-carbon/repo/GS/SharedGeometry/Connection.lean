module

public import GS.SharedGeometry.Gradient
public import GS.GlobalGeometry.ProjectedDerivative

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The induced projected connection along shared-orbit curves

The operation below takes values in the actual tangent fibre of the shared
atlas. Its ambient realization is the orthogonal projection of the ordinary
derivative. The pairing and product rules use the induced physical Frobenius
metric; no unweighted metric on the unique blocks is substituted.

This supplies the extrinsic induced-connection interface used by the concrete
geodesic theorem. It is not a registration of a general bundled connection API.
-/
set_option autoImplicit false
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions
open scoped Topology Manifold
namespace GS.SharedGeometry
variable {n : ℕ} (right left : Pattern n) (P : Mat n)
local instance connectionNormedSpace : NormedSpace ℝ (HorizontalModel right left P) := Submodule.normedSpace _
local instance connectionChartedSpace : ChartedSpace (HorizontalModel right left P) (MatrixOrbit right left P) :=
  sharedOrbitChartedSpace right left P
local instance connectionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel right left P)) ⊤
    (MatrixOrbit right left P) := sharedOrbitIsManifold right left P

/-- Projection of the actual ambient derivative into the actual tangent fibre. -/
def covariantAlong (γ : ℝ → MatrixOrbit right left P) (V : ℝ → Mat n) (t : ℝ) :
    TangentSpace (𝓘(ℝ, HorizontalModel right left P)) (γ t) :=
  tangentProjection right left P (γ t) (deriv V t)

@[simp] theorem inclusion_covariantAlong (γ : ℝ → MatrixOrbit right left P)
    (V : ℝ → Mat n) (t : ℝ) :
    inclusionDifferential right left P (γ t) (covariantAlong right left P γ V t) =
      pointProjection right left (γ t).val (deriv V t) :=
  inclusion_tangentProjection right left P (γ t) _

end GS.SharedGeometry
