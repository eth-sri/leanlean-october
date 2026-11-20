module

public import GS.OverlapGeometry.GeodesicDynamics
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Metric compatibility and symmetric Christoffel coefficients

The projected derivative uses the actual tangent fibres and their Frobenius
metric. In the preferred horizontal coordinates, its Christoffel coefficients
come from the genuine second Frechet derivative of the inverse chart. Schwarz's
theorem proves symmetry. A differentiated coordinate metric proves metric
compatibility. These are the local Levi-Civita characterization identities;
registration as a global bundled mathlib connection is a separate interface.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.GlobalGeometry
open GS.LieAction GS.CayleyCharts GS.ManifoldCompletion
open scoped Topology Manifold
namespace GS.OverlapGeometry

variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance connectionHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance connectionChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance connectionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

end GS.OverlapGeometry
