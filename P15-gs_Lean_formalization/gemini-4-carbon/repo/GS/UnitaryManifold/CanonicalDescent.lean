module

public import GS.UnitaryManifold.BundleRetraction
public import GS.UnitaryManifold.Gradient
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Descent through the canonical whole-bundle unitary Cayley retraction

This module leaves the older chosen-chart descent API unchanged.  The curve
used here is the canonical point-and-tangent construction from BundleRetraction,
with its already established actual matrix velocity.  Its negative intrinsic
gradient has loss derivative minus the squared induced metric norm.  Armijo
steps exist and geometric backtracking terminates for a nonzero gradient.

No convergence rate or floating-point implementation theorem is asserted.
-/

set_option autoImplicit false

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.RiemannianCompletion Filter
open scoped Topology Manifold
namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance canonicalDescentHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance canonicalDescentHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance canonicalDescentChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance canonicalDescentIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- Exact agreement with evaluation of the new map on the whole tangent bundle. -/
@[simp] theorem cayleyRetraction_scaled (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    cayleyRetraction b₁ b₂ σ ⟨X, t • v⟩ = canonicalCayleyStep b₁ b₂ σ X v t := by
  change canonicalCayleyStep b₁ b₂ σ X (t • v) 1 = _
  simpa only [one_mul] using canonicalCayleyStep_smul b₁ b₂ σ X v t 1

end GS.UnitaryManifold
