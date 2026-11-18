module

public import GS.GlobalGeometry.IntrinsicCayley
public import GS.OverlapGeometry.Gradient
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# A Cayley retraction on every actual tangent fibre, allowing overlap

The orbit retains the horizontal atlas and inherited matrix topology. The
Cayley curve is globally defined, is smooth jointly in velocity and time at
any fixed base point, and its actual manifold derivative is the prescribed
tangent vector. The time-one map has derivative equal to the identity at zero.
These are fibrewise statements; no total tangent-bundle smoothness is claimed.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.GlobalGeometry Filter
open scoped Topology Manifold
namespace GS.OverlapGeometry
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance retractionHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance retractionChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance retractionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- A globally defined curve into the original orbit, indexed by an actual
TangentSpace vector. The factor choice is used only to certify membership. -/
def cayleyTangentStep (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    MatrixOrbit b₁ b₂ (permMatrix σ) :=
  orbitMapToOrbit b₁ b₂ (permMatrix σ)
    (pointStepFactors (preferredFactor σ X) X.val (inclusionDifferential b₁ b₂ σ X v) t)

@[simp] theorem cayleyTangentStep_val (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    (cayleyTangentStep b₁ b₂ σ X v t).val =
      pointCayleyStep b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) t := by
  let g := preferredFactor σ X
  let U := unitCayley (t • balancedLeft b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v))
  let V := unitCayley (t • balancedRight b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v))
  change (U * g.1.val) * permMatrix σ * (Vᵀ * g.2.val)ᵀ = U * X.val * V
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hg : g.1.val * permMatrix σ * g.2.valᵀ = X.val :=
    congrArg Subtype.val (preferredFactor_spec σ X)
  calc
    (U * g.1.val) * permMatrix σ * (g.2.valᵀ * V) =
        U * (g.1.val * permMatrix σ * g.2.valᵀ) * V := by simp only [Matrix.mul_assoc]
    _ = U * X.val * V := by rw [hg]

@[simp] theorem cayleyTangentStep_at_zero (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,HorizontalModel b₁ b₂ σ)) X) : cayleyTangentStep b₁ b₂ σ X v 0=X := by
  apply Subtype.ext
  simp

@[simp] theorem cayleyTangentStep_zero_vector (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (t : ℝ) : cayleyTangentStep b₁ b₂ σ X 0 t=X := by
  apply Subtype.ext
  simp

/-- The time-one Cayley retraction on the actual tangent fibre. -/
def cayleyFibreRetraction (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    MatrixOrbit b₁ b₂ (permMatrix σ) :=
  cayleyTangentStep b₁ b₂ σ X v 1

@[simp] theorem cayleyFibreRetraction_val (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    (cayleyFibreRetraction b₁ b₂ σ X v).val =
      pointCayleyStep b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) 1 :=
  cayleyTangentStep_val b₁ b₂ σ X v 1

@[simp] theorem cayleyFibreRetraction_zero (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    cayleyFibreRetraction b₁ b₂ σ X 0 = X :=
  cayleyTangentStep_zero_vector b₁ b₂ σ X 1

end GS.OverlapGeometry
