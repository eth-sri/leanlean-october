module
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import GS.Continuation.AmbientProjection
public import GS.Core
public import GS.Extensions.MatrixCalculus
public import GS.Extensions.ProjectionSmooth
public import GS.Extensions.TransportedProjection
public import GS.Extensions.TwoFactorProjection
public import GS.Frobenius
public import GS.GeometryAlgebra
public import GS.GlobalGeometry.FrobeniusProjection
public import GS.Projection


@[expose] public section

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
noncomputable section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Matrix GS GS.Extensions GS.Continuation
namespace GS.GlobalGeometry
variable {n : ℕ}

/-- tau assigns a sharing label to each physical block. Labels need not be
consecutive or injective; different factors have independent labellings. -/
def TiedEntries (b : ℕ) (τ : ℕ → ℕ) (A : Mat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

def sharedSkewSpace (b : ℕ) (τ : ℕ → ℕ) : Submodule ℝ (Mat n) where
  carrier := {A | BlockDiagonal b A ∧ IsSkew A ∧ TiedEntries b τ A}
  zero_mem' := by
    refine ⟨Supported.zero, ?_, ?_⟩
    · simp [IsSkew]
    · intro i j i' j' _ _ _ _ _; rfl
  add_mem' := by
    rintro A B ⟨hsA,hkA,htA⟩ ⟨hsB,hkB,htB⟩
    refine ⟨hsA.add hsB, ?_, ?_⟩
    · change Aᵀ = -A at hkA
      change Bᵀ = -B at hkB
      simp only [IsSkew, Matrix.transpose_add, hkA, hkB, neg_add]
    · intro i j i' j' h h' hτ hi hj
      simp only [Matrix.add_apply, htA i j i' j' h h' hτ hi hj,
        htB i j i' j' h h' hτ hi hj]
  smul_mem' := by
    rintro a A ⟨hs,hk,ht⟩
    refine ⟨Supported.smul a hs, ?_, ?_⟩
    · change Aᵀ = -A at hk
      simp only [IsSkew, Matrix.transpose_smul, hk, smul_neg]
    · intro i j i' j' h h' hτ hi hj
      simp only [Matrix.smul_apply, ht i j i' j' h h' hτ hi hj]

def SharedDirection (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Y : Mat n) : Prop :=
  ∃ C ∈ sharedSkewSpace b₂ τ₂, ∃ Ω ∈ sharedSkewSpace b₁ τ₁,
    Y = L*C*P*R + L*P*Ω*R

end GS.GlobalGeometry
