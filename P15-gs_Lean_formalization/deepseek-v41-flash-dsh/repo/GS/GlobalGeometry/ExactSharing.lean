module

public import GS.GlobalGeometry.FrobeniusProjection
public import GS.Continuation.AmbientProjection
public import GS.Extensions.ProjectionSmooth
public import Mathlib.Analysis.Calculus.ContDiff.Operations

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

/-- Two actual shared generator spaces, not free parameters for a projector. -/
def sharedCoreMap (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) :
    (sharedSkewSpace (n := n) b₂ τ₂ × sharedSkewSpace (n := n) b₁ τ₁) →ₗ[ℝ] Mat n where
  toFun v := v.1.val + P * v.2.val * Pᵀ
  map_add' v w := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add,
      Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' a v := by
    change (a • v.1.val) + P * (a • v.2.val) * Pᵀ =
      a • (v.1.val + P * v.2.val * Pᵀ)
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_add]

def sharedCore (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P : Mat n) : Submodule ℝ (Mat n) :=
  LinearMap.range (sharedCoreMap b₁ b₂ τ₁ τ₂ P)

def SharedDirection (b₁ b₂ : ℕ) (τ₁ τ₂ : ℕ → ℕ) (P L R Y : Mat n) : Prop :=
  ∃ C ∈ sharedSkewSpace b₂ τ₂, ∃ Ω ∈ sharedSkewSpace b₁ τ₁,
    Y = L*C*P*R + L*P*Ω*R

end GS.GlobalGeometry
