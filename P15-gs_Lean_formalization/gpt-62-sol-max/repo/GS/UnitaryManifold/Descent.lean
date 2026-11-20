module

public import GS.UnitaryManifold.Retraction
public import GS.UnitaryManifold.Gradient
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Intrinsic Cayley descent with arbitrary overlap

The negative intrinsic gradient is an actual vector in the tangent space of
the horizontal orbit atlas. Its fixed-base Cayley curve has the negative squared metric
norm as loss derivative, satisfies Armijo decrease for all sufficiently small
positive steps, and permits finite geometric backtracking.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.RiemannianCompletion Filter
open scoped Topology Manifold
namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance unitaryDescentHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance unitaryDescentHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance unitaryDescentChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance unitaryDescentIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- A feasible curve on a fixed tangent fibre; the base point is not varied. -/
def fibreRetractionStep (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    MatrixOrbit b₁ b₂ (cPermMatrix σ) := fibreRetraction b₁ b₂ σ X (t • v)

@[simp] theorem fibreRetractionStep_at_zero (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    fibreRetractionStep b₁ b₂ σ X v 0 = X := by
  simp [fibreRetractionStep]

end GS.UnitaryManifold
