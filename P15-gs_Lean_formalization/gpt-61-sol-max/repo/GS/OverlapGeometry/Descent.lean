module

public import GS.OverlapGeometry.Retraction
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Intrinsic Cayley descent with arbitrary overlap

The negative intrinsic gradient is an actual vector in the tangent space of
the horizontal orbit atlas. Its Cayley curve has the negative squared metric
norm as loss derivative, satisfies Armijo decrease for all sufficiently small
positive steps, and permits finite geometric backtracking.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.RiemannianCompletion Filter
open scoped Topology Manifold
namespace GS.OverlapGeometry
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance descentHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance descentChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance descentIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

end GS.OverlapGeometry
