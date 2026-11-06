module

public import GS.GlobalGeometry.SharedFactorCurves
public import GS.RiemannianCompletion.ExponentialStep
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

noncomputable section
open Matrix GS
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- The image of the actual tied orthogonal factors. -/
def InSharedA2Orth (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : Mat n) : Prop :=
  ∃ L R, SharedOrthogonalFactor b₂ τ₂ L ∧ SharedOrthogonalFactor b₁ τ₁ R ∧
    X = product2 L P R

end GS.GlobalGeometry
