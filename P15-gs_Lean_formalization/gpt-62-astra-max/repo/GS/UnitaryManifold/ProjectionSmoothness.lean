module

public import GS.Unitary.SmoothPointProjection
public import GS.UnitaryManifold.PointProjection

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-! Joint smoothness of the actual unitary tangent projection as its matrix
base point and ambient direction vary. The orbit has the inherited topology. -/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix GS.UnitaryGeometry
open scoped Topology Manifold
namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance projectorSmoothHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance projectorSmoothHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

end GS.UnitaryManifold
