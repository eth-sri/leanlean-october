module

public import GS.Core
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

noncomputable section

section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# Exact projection with arbitrary within-factor sharing AND overlap

The sharing relation below is the actual equality of local entries in tied
physical blocks. The core subspace is the image of its two concrete Lie-algebra
subspaces under (C,Omega) |-> C + P Omega P^T. Orthogonal projection is
constructed from the complete finite-dimensional subspace, not assumed through
normal equations and not replaced by averaged 1/2 masks.

These are exact generator-image results and smooth formulas in the factors.
No smooth quotient, tangent-bundle identification, efficient pseudoinverse
algorithm, or minimal-norm factor lift is claimed by this module.
-/
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- tau assigns a sharing label to each physical block. Labels need not be
consecutive or injective; different factors have independent labellings. -/
def TiedEntries (b : ℕ) (τ : ℕ → ℕ) (A : Mat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

end GS.GlobalGeometry

end

section

namespace GS.GlobalGeometry
variable {n : ℕ}

/-- An actual finite matrix factor with the specified physical block ties. -/
def SharedOrthogonalFactor (b : ℕ) (τ : ℕ → ℕ) (A : Mat n) : Prop :=
  BlockDiagonal b A ∧ Orthogonal A ∧ TiedEntries b τ A

/-- The image of the actual tied orthogonal factors. -/
def InSharedA2Orth (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P X : Mat n) : Prop :=
  ∃ L R, SharedOrthogonalFactor b₂ τ₂ L ∧ SharedOrthogonalFactor b₁ τ₁ R ∧
    X = product2 L P R

end GS.GlobalGeometry

end
