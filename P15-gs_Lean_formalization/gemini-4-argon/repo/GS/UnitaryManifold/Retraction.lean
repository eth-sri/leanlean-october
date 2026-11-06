module

public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

public import GS.UnitaryManifold.TangentBridge
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A smooth retraction on every fixed unitary tangent fibre

The preferred horizontal Cayley parametrization is globally defined in its
coordinate vector and has the correct derivative at the centre. It therefore
gives a retraction from each actual tangent fibre. All smoothness statements
keep the base point fixed. No smooth dependence of the chosen preferred
factorization on the base point, or total tangent-bundle retraction, is asserted.
-/
noncomputable section
set_option synthInstance.maxHeartbeats 100000
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open GS Matrix GS.UnitaryGeometry GS.OverlapGeometry
open scoped Topology Manifold
namespace GS.UnitaryManifold
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance retractionHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance retractionHorizontalNormedSpace :
    NormedSpace ℝ (HorizontalModel b₁ b₂ σ) := Submodule.normedSpace _
local instance retractionChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance retractionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- The globally defined horizontal Cayley parametrization of a fixed tangent fibre. -/
def fibreRetraction (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    MatrixOrbit b₁ b₂ (cPermMatrix σ) :=
  (preferredOrbitSlice b₁ b₂ σ X).parametrization v

@[simp] theorem fibreRetraction_val (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    (fibreRetraction b₁ b₂ σ X v).val = preferredFactor σ X • horizontalValue b₁ b₂ σ v := rfl

@[simp] theorem fibreRetraction_zero (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    fibreRetraction b₁ b₂ σ X 0 = X := by
  have hh := (preferredOrbitSlice b₁ b₂ σ X).left_inverse X
    (preferredOrbitSlice_covers b₁ b₂ σ X)
  rw [preferredOrbitSlice_coordinates_zero] at hh
  exact hh

end GS.UnitaryManifold
