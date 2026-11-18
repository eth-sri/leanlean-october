module

public import GS.GlobalGeometry.IntrinsicCayley
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Intrinsic Cayley velocity and certified descent

The Cayley curve is smooth as a map into the actual orbit manifold, and its
mathlib manifold derivative at zero is the prescribed tangent vector. The
negative intrinsic gradient gives an Armijo decrease for every sufficiently
small positive step. These conclusions require only differentiability of the
loss at the current point, with no assumed gradient oracle or convergence claim.
-/

noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation GS.LieAction GS.CayleyCharts
open GS.ManifoldCompletion GS.RiemannianCompletion Filter
open scoped Topology Manifold

namespace GS.GlobalGeometry

variable {n : ℕ} {b₁ b₂ : Fin n → ℕ}
variable (σ : Equiv.Perm (Fin n)) [Fact (NoOffDiagonalOverlap b₁ b₂ σ)]

/-- The time-one Cayley retraction on the actual tangent fibre. -/
def cayleyFibreRetraction (X : MatrixOrbit b₁ b₂ (permMatrix σ))
    (v : TangentSpace (𝓘(ℝ, PairModel b₁ b₂)) X) :
    MatrixOrbit b₁ b₂ (permMatrix σ) :=
  cayleyTangentStep (b₁ := b₁) (b₂ := b₂) σ X v 1

@[simp] theorem cayleyFibreRetraction_zero (X : MatrixOrbit b₁ b₂ (permMatrix σ)) :
    cayleyFibreRetraction (b₁ := b₁) (b₂ := b₂) σ X 0 = X :=
  cayleyTangentStep_zero_vector (b₁ := b₁) (b₂ := b₂) σ X 1

end GS.GlobalGeometry
