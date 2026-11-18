module

public import GS.GlobalGeometry.CayleyRetraction
public import GS.RiemannianCompletion.Gradient
public import GS.ManifoldCompletion.OrbitSmooth

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Cayley update on the genuine non-overlap orbit and in tangent charts

We prove a general criterion: a matrix-smooth map to the factor group induces
a manifold-smooth map to the orbit. A fixed stabilizer element, held constant
on a neighbourhood, supplies the proof; no smooth preferredFactor is assumed.
The new point-only update has globally smooth tangent-coordinate expressions
with values in the actual orbit. It is also defined for actual TangentSpace
vectors and has the correct actual matrix derivative at zero.

No generic mathlib Retraction structure or smooth total tangent-bundle section
is invented. The chart criterion is explicit; a final total-space registration
is listed separately. Overlap statements in CayleyRetraction remain independent
of this file's no-overlap manifold assumptions.
-/
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.RiemannianCompletion Filter
open scoped Topology Manifold
namespace GS.GlobalGeometry
variable {n : ℕ} {b₁ b₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n)) [hno : Fact (NoOffDiagonalOverlap b₁ b₂ σ)]

/-- All denominators are invertible because the arguments are skew. -/
def pointStepFactors (g : FactorGroup b₁ b₂) (X Z : Mat n) (t : ℝ) :
    FactorGroup b₁ b₂ :=
  (⟨unitCayley (t•balancedLeft b₁ b₂ X Z),
      unitCayley_supported _ _ ((balancedLeft_supported _ _ _ _).smul t)
        (isSkew_smul t (balancedLeft_skew _ _ _ _)),
      unitCayley_orthogonal _ (isSkew_smul t (balancedLeft_skew _ _ _ _))⟩ * g.1,
   ⟨(unitCayley (t•balancedRight b₁ b₂ X Z))ᵀ,
      (unitCayley_supported _ _ ((balancedRight_supported _ _ _ _).smul t)
        (isSkew_smul t (balancedRight_skew _ _ _ _))).transpose,
      (unitCayley_orthogonal _ (isSkew_smul t (balancedRight_skew _ _ _ _))).transpose⟩ * g.2)

theorem pointStepFactors_value (g : FactorGroup b₁ b₂) (X Z : Mat n) (t : ℝ)
    (hg : g • permMatrix σ = X) :
    pointStepFactors g X Z t • permMatrix σ = pointCayleyStep b₁ b₂ X Z t := by
  let U := unitCayley (t • balancedLeft b₁ b₂ X Z)
  let V := unitCayley (t • balancedRight b₁ b₂ X Z)
  change (U * g.1.val) * permMatrix σ * (Vᵀ * g.2.val)ᵀ = U * X * V
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]
  calc
    (U * g.1.val) * permMatrix σ * (g.2.valᵀ * V) =
        U * (g.1.val * permMatrix σ * g.2.valᵀ) * V := by simp only [Matrix.mul_assoc]
    _ = U * X * V := by rw [show g.1.val * permMatrix σ * g.2.valᵀ = X from hg]

/-- A globally defined curve into the original orbit, indexed by an actual
TangentSpace vector. The factor choice is used only to certify membership. -/
def cayleyTangentStep (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) (t : ℝ) :
    MatrixOrbit b₁ b₂ (permMatrix σ) :=
  orbitMapToOrbit b₁ b₂ (permMatrix σ)
    (pointStepFactors (preferredFactor σ X) X.val (inclusionDifferential σ X v) t)

@[simp] theorem cayleyTangentStep_val (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) (t : ℝ) :
    (cayleyTangentStep σ X v t).val =
      pointCayleyStep b₁ b₂ X.val (inclusionDifferential σ X v) t :=
  pointStepFactors_value σ _ _ _ t (congrArg Subtype.val (preferredFactor_spec σ X))

@[simp] theorem cayleyTangentStep_at_zero (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ,PairModel b₁ b₂)) X) : cayleyTangentStep σ X v 0=X := by
  apply Subtype.ext
  simp

@[simp] theorem cayleyTangentStep_zero_vector (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (t : ℝ) : cayleyTangentStep σ X 0 t=X := by
  apply Subtype.ext
  simp

end GS.GlobalGeometry
