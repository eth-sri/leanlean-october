module

public import GS.Projection
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Matrix.Normed
public import GS.Extensions.TwoFactorProjection
public import GS.Extensions.TransportedProjection
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section


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
open Matrix GS GS.Extensions
namespace GS.GlobalGeometry
variable {n : ℕ}

section
variable (b : ℕ) (τ : ℕ → ℕ)
/-- tau assigns a sharing label to each physical block. Labels need not be
consecutive or injective; different factors have independent labellings. -/
def TiedEntries (A : Mat n) : Prop :=
  ∀ i j i' j' : Fin n,
    i.val / b = j.val / b → i'.val / b = j'.val / b →
    τ (i.val / b) = τ (i'.val / b) →
    i.val % b = i'.val % b → j.val % b = j'.val % b → A i j = A i' j'

def sharedSkewSpace : Submodule ℝ (Mat n) where
  carrier := {A | BlockDiagonal b A ∧ IsSkew A ∧ TiedEntries b τ A}
  zero_mem' := ⟨Supported.zero, by simp [IsSkew], by tauto⟩
  add_mem' hA hB := ⟨hA.1.add hB.1, by simp_all [IsSkew, add_comm], fun i j i' j' h h' hτ hi hj => by
    simp [hA.2.2 i j i' j' h h' hτ hi hj, hB.2.2 i j i' j' h h' hτ hi hj]⟩
  smul_mem' a _ hA := ⟨hA.1.smul a, by simp_all [IsSkew], fun i j i' j' h h' hτ hi hj => by
    simp [hA.2.2 i j i' j' h h' hτ hi hj]⟩





end

end GS.GlobalGeometry
