module

public import GS.UnitaryManifold.PointCayley
public import GS.UnitaryManifold.Gradient
public import GS.OverlapGeometry.ManifoldSmoothMaps
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
The final construction is smooth on mathlib's whole tangent bundle.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.UnitaryGeometry GS.OverlapGeometry Filter
open scoped Topology Manifold
namespace GS.UnitaryManifold
set_option synthInstance.maxHeartbeats 100000
variable {n : ℕ} (b₁ b₂ : Fin n → ℕ) (σ : Equiv.Perm (Fin n))
local instance canonicalRetractionHorizontalNormedAddCommGroup :
    NormedAddCommGroup (HorizontalModel b₁ b₂ σ) := inferInstance
local instance canonicalRetractionHorizontalNormedSpace : NormedSpace ℝ (HorizontalModel b₁ b₂ σ) :=
  Submodule.normedSpace _
local instance canonicalRetractionChartedSpace : ChartedSpace (HorizontalModel b₁ b₂ σ)
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapChartedSpace b₁ b₂ σ
local instance canonicalRetractionIsManifold : IsManifold (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) ⊤
    (MatrixOrbit b₁ b₂ (cPermMatrix σ)) := overlapIsManifold b₁ b₂ σ

/-- The matrix value contains no preferred-factor choice. The orbit witness
is a proposition and cannot affect the output of this subtype-valued function. -/
def canonicalCayleyStep (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    MatrixOrbit b₁ b₂ (cPermMatrix σ) :=
  ⟨pointCayleyStep b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) t,
    pointCayleyStep_mem_orbit b₁ b₂ (cPermMatrix σ) X.val
      (inclusionDifferential b₁ b₂ σ X v) X.property t⟩

@[simp] theorem canonicalCayleyStep_val (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (t : ℝ) :
    (canonicalCayleyStep b₁ b₂ σ X v t).val =
      pointCayleyStep b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) t := rfl

@[simp] theorem canonicalCayleyStep_at_zero (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ,HorizontalModel b₁ b₂ σ)) X) : canonicalCayleyStep b₁ b₂ σ X v 0=X := by
  apply Subtype.ext
  simp

@[simp] theorem canonicalCayleyStep_zero_vector (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (t : ℝ) : canonicalCayleyStep b₁ b₂ σ X 0 t=X := by
  apply Subtype.ext
  simp

/-- Scaling the tangent vector is equivalent to scaling time. -/
theorem canonicalCayleyStep_smul
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) (a t : ℝ) :
    canonicalCayleyStep b₁ b₂ σ X (a • v) t = canonicalCayleyStep b₁ b₂ σ X v (t * a) := by
  apply Subtype.ext
  simp only [canonicalCayleyStep_val, map_smul, pointCayleyStep,
    balancedLeft_smul, balancedRight_smul, smul_smul]

/-- The time-one Cayley retraction on the actual tangent fibre. -/
def canonicalFibreRetraction (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    MatrixOrbit b₁ b₂ (cPermMatrix σ) :=
  canonicalCayleyStep b₁ b₂ σ X v 1

@[simp] theorem canonicalFibreRetraction_val (X : MatrixOrbit b₁ b₂ (cPermMatrix σ))
    (v : TangentSpace (𝓘(ℝ, HorizontalModel b₁ b₂ σ)) X) :
    (canonicalFibreRetraction b₁ b₂ σ X v).val =
      pointCayleyStep b₁ b₂ X.val (inclusionDifferential b₁ b₂ σ X v) 1 :=
  canonicalCayleyStep_val b₁ b₂ σ X v 1

@[simp] theorem canonicalFibreRetraction_zero (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    canonicalFibreRetraction b₁ b₂ σ X 0 = X :=
  canonicalCayleyStep_zero_vector b₁ b₂ σ X 1

/-- The domain is mathlib's actual tangent bundle, with its standard topology
and smooth structure, not a product chosen separately for each base point. -/
def cayleyRetraction
    (p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (cPermMatrix σ))) : MatrixOrbit b₁ b₂ (cPermMatrix σ) :=
  canonicalFibreRetraction b₁ b₂ σ p.proj p.2

@[simp] theorem cayleyRetraction_val
    (p : TangentBundle (𝓘(ℝ, HorizontalModel b₁ b₂ σ))
      (MatrixOrbit b₁ b₂ (cPermMatrix σ))) :
    (cayleyRetraction b₁ b₂ σ p).val =
      pointCayleyStep b₁ b₂ p.proj.val
        (tangentAmbient b₁ b₂ σ p) 1 :=
  canonicalFibreRetraction_val b₁ b₂ σ p.proj p.2

@[simp] theorem cayleyRetraction_zero_section
    (X : MatrixOrbit b₁ b₂ (cPermMatrix σ)) :
    cayleyRetraction b₁ b₂ σ ⟨X, 0⟩ = X :=
  canonicalFibreRetraction_zero b₁ b₂ σ X

end GS.UnitaryManifold
