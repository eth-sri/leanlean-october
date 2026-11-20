module

public import GS.OverlapGeometry.GeodesicConnection
public import GS.Continuation.ExponentialCurves

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Block exponential curves in the matrix orbit

The target is the original matrix-orbit subtype, with its inherited topology
and the arbitrary-overlap horizontal atlas. The curve, its actual first and
second derivatives, its genuine tangent velocity and its projected covariant
acceleration are related explicitly. Under no off-diagonal overlap the latter
vanishes for every time. No differential-equation or chart assumptions occur.

The connection operation is the previously established projected derivative
for the induced Frobenius metric. This module does not replace a library
geodesic predicate by a newly defined predicate.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.OverlapGeometry
open scoped Topology Manifold
namespace GS.Geodesics

variable {n : ℕ}

variable (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) := Submodule.normedSpace _
local instance : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (permMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- Concrete supported orthogonal factors, defined for every real time. The
second group coordinate is transposed because the orbit action is L P R^T. -/
def blockExpFactors (g : FactorGroup b₁ b₂) (C : Model b₂) (Ω : Model b₁)
    (t : ℝ) : FactorGroup b₁ b₂ :=
  (⟨gsExpLeft g.1.val C.val t,
     gsExpLeft_supported _ _ g.1.property.1 C.property.1 t,
     gsExpLeft_orthogonal _ _ g.1.property.2 C.property.2 t⟩,
   ⟨(gsExpRight g.2.valᵀ Ω.val t)ᵀ,
     (gsExpRight_supported _ _ g.2.property.1.transpose Ω.property.1 t).transpose,
     (gsExpRight_orthogonal _ _ g.2.property.2.transpose Ω.property.2 t).transpose⟩)

/-- An actual curve in the original matrix orbit, not a quotient-only curve. -/
def blockExpCurve (g : FactorGroup b₁ b₂) (C : Model b₂) (Ω : Model b₁)
    (t : ℝ) : MatrixOrbit b₁ b₂ (permMatrix σ) :=
  orbitMapToOrbit b₁ b₂ (permMatrix σ) (blockExpFactors b₁ b₂ g C Ω t)

@[simp] theorem blockExpCurve_val (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) (t : ℝ) :
    (blockExpCurve b₁ b₂ σ g C Ω t).val =
      gsExpCurve g.1.val (permMatrix σ) g.2.valᵀ C.val Ω.val t := by
  change gsExpLeft _ _ t * permMatrix σ * ((gsExpRight _ _ t)ᵀ)ᵀ = _
  simp only [Matrix.transpose_transpose, gsExpCurve, product2]

@[simp] theorem blockExpCurve_zero (g : FactorGroup b₁ b₂)
    (C : Model b₂) (Ω : Model b₁) :
    blockExpCurve b₁ b₂ σ g C Ω 0 = orbitMapToOrbit b₁ b₂ (permMatrix σ) g := by
  apply Subtype.ext
  simp only [blockExpCurve_val, gsExpCurve_zero]
  rfl

end GS.Geodesics
