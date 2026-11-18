module

public import GS.OverlapGeometry.Gradient
public import GS.GlobalGeometry.ProjectedDerivative

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Moving-generator acceleration with arbitrary overlap

The actual second derivative is computed before projection. The result gives
an explicit evolution equation in the fixed sum of the two supported Lie
algebras. The commutator term is retained; it need not vanish with overlap.
The projected operation is also lifted into the actual tangent space of the
horizontal atlas and paired with its established Frobenius metric.

This module does not register a bundled Levi-Civita connection or assert an
existence theorem for solutions of the resulting differential equation.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
attribute [local instance] Classical.propDecidable
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry
open GS.LieAction GS.CayleyCharts GS.ManifoldCompletion
open scoped Topology Manifold
namespace GS.OverlapGeometry

variable {n : ℕ}

section ActualTangent
variable (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance geodesicHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance geodesicChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance geodesicIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

def covariantAlong (γ : ℝ → MatrixOrbit b₁ b₂ (permMatrix σ))
    (V : ℝ → Mat n) (t : ℝ) :
    TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) (γ t) :=
  tangentProjection b₁ b₂ σ (γ t) (deriv V t)

@[simp] theorem inclusion_covariantAlong
    (γ : ℝ → MatrixOrbit b₁ b₂ (permMatrix σ)) (V : ℝ → Mat n) (t : ℝ) :
    inclusionDifferential b₁ b₂ σ (γ t) (covariantAlong b₁ b₂ σ γ V t) =
      pointProjection b₁ b₂ (γ t).val (deriv V t) :=
  inclusion_tangentProjection b₁ b₂ σ (γ t) (deriv V t)

end ActualTangent
end GS.OverlapGeometry
