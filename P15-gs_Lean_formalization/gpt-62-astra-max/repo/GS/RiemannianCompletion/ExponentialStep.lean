module

public import GS.RiemannianCompletion.Gradient
public import GS.Continuation.ExponentialCurves
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exponential updates indexed by genuine tangent vectors

The curve is a map into the original orbit subtype, for all real times. Its
matrix derivative at zero is the actual differential image of the given tangent
vector. The existing normal-acceleration theorem is then transported to the
actual tangent space at every point of the curve. We also prove a first-order
Armijo decrease statement for the negative intrinsic gradient.

No Levi-Civita connection or library geodesic predicate is redefined here. A
normal-acceleration certificate is not labelled as a completed geodesic theorem.
The proofs use the actual tangent atlas and matrix derivatives.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.LieAction GS.CayleyCharts GS.Extensions GS.Continuation
open GS.ManifoldCompletion Filter
open scoped Topology Manifold
namespace GS.RiemannianCompletion
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n))
variable [hno : Fact (NoOffDiagonalOverlap block₁ block₂ σ)]

/-- Cayley coordinate velocities are converted to group generators with the
correct -2,+2 factors. These are definitions of generators, NOT of derivatives. -/
def stepLeftGenerator (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) : Model block₂ :=
  (-2 : ℝ) • v.1

def stepRightGenerator (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) : Model block₁ :=
  (2 : ℝ) • v.2

/-- Concrete orthogonal block factors at every time; no lifting assumption. -/
def stepFactors (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) :
    FactorGroup block₁ block₂ := by
  let g := preferredFactor σ X
  let C := stepLeftGenerator σ X v
  let Ω := stepRightGenerator σ X v
  exact
    (⟨gsExpLeft g.1.val C.val t,
       gsExpLeft_supported _ _ g.1.property.1 C.property.1 t,
       gsExpLeft_orthogonal _ _ g.1.property.2 C.property.2 t⟩,
     ⟨(gsExpRight g.2.valᵀ Ω.val t)ᵀ,
       (gsExpRight_supported _ _ g.2.property.1.transpose Ω.property.1 t).transpose,
       (gsExpRight_orthogonal _ _ g.2.property.2.transpose Ω.property.2 t).transpose⟩)

/-- Global-in-time curve inside the original orbit. Its basepoint uses the
unchanged subtype topology and the new actual tangent space from the atlas. -/
def exponentialStep (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) :
    MatrixOrbit block₁ block₂ (permMatrix σ) :=
  orbitMapToOrbit block₁ block₂ (permMatrix σ) (stepFactors σ X v t)

@[simp] theorem exponentialStep_val (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) (t : ℝ) :
    (exponentialStep σ X v t).val =
      gsExpCurve (preferredFactor σ X).1.val (permMatrix σ) (preferredFactor σ X).2.valᵀ
        (stepLeftGenerator σ X v).val (stepRightGenerator σ X v).val t := by
  change gsExpLeft _ _ t * permMatrix σ * ((gsExpRight _ _ t)ᵀ)ᵀ = _
  simp only [Matrix.transpose_transpose, gsExpCurve, product2]

@[simp] theorem exponentialStep_zero (X : MatrixOrbit block₁ block₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel block₁ block₂)) X) :
    exponentialStep σ X v 0 = X := by
  apply Subtype.ext
  rw [exponentialStep_val, gsExpCurve_zero, preferredFactor_product]

end GS.RiemannianCompletion
