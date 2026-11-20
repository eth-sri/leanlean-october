module

public import GS.OverlapGeometry.Retraction
public import GS.OverlapGeometry.ManifoldSmoothMaps

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A smooth Cayley retraction on the complete tangent bundle

The map uses the base matrix and its actual ambient tangent vector. It is
defined on the whole tangent bundle, is smooth jointly in both variables,
fixes the zero section, and has identity differential along each zero fibre.
Independent blocks with arbitrary overlap are allowed.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.ManifoldCompletion
open scoped Topology Manifold

namespace GS.OverlapGeometry

variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))

local instance : NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) := Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- The domain is mathlib's actual tangent bundle, with its standard topology
and smooth structure, not a product chosen separately for each base point. -/
def cayleyRetraction
    (p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (permMatrix σ))) : MatrixOrbit b₁ b₂ (permMatrix σ) :=
  cayleyFibreRetraction b₁ b₂ σ p.proj p.2

@[simp] theorem cayleyRetraction_val
    (p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (permMatrix σ))) :
    (cayleyRetraction b₁ b₂ σ p).val =
      GS.GlobalGeometry.pointCayleyStep b₁ b₂ p.proj.val
        (tangentAmbient b₁ b₂ σ p) 1 :=
  cayleyFibreRetraction_val b₁ b₂ σ p.proj p.2

@[simp] theorem cayleyRetraction_zero_section
    (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    cayleyRetraction b₁ b₂ σ ⟨X, 0⟩ = X :=
  cayleyFibreRetraction_zero b₁ b₂ σ X

end GS.OverlapGeometry
