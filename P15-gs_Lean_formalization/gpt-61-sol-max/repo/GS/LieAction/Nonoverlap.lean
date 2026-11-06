module

public import GS.LieAction.CompactQuotient
public import GS.Shuffle
public import GS.GeometryAlgebra

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-!
# The stabilizer in the real orthogonal non-overlap case

The entire O-block stabilizer is described, not just its tangent space.
It is equivalent to the 2^n diagonal sign matrices. This statement is for O,
not SO: separate determinant constraints would reduce the sign choices.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace GS.LieAction
variable {n : ℕ} {block₁ block₂ : Fin n → ℕ}

/-- Each intersection of a right block and a pulled-back left block contains
at most one coordinate. This is the exact no-offdiagonal-overlap condition. -/
def NoOffDiagonalOverlap (block₁ block₂ : Fin n → ℕ)
    (σ : Equiv.Perm (Fin n)) : Prop :=
  Function.Injective (fun i => (block₁ i, block₂ (σ i)))

theorem common_matrix_diagonal (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ) {T : Mat n}
    (h₁ : Supported block₁ T) (h₂ : Supported (fun i => block₂ (σ i)) T) :
    T = Matrix.diagonal (fun i => T i i) := by
  ext i j
  by_cases hij : i = j
  · subst j; simp
  · have ht : T i j = 0 := by
      by_cases h : block₁ i = block₁ j
      · have h' : block₂ (σ i) ≠ block₂ (σ j) := by
          intro h''
          exact hij (hn (Prod.ext h h''))
        exact h₂ i j h'
      · exact h₁ i j h
    simpa [Matrix.diagonal, hij] using ht

theorem commonRight_diagonal (σ : Equiv.Perm (Fin n))
    (hn : NoOffDiagonalOverlap block₁ block₂ σ)
    (T : commonRightSubgroup block₁ block₂ (permMatrix σ) (perm_orthogonal σ)) :
    T.val.val = Matrix.diagonal (fun i => T.val.val i i) :=
  common_matrix_diagonal σ hn T.val.property.1
    ((commonRight_mem_iff σ T.val).mp T.property)

theorem orthogonal_diagonal_sign {T : Mat n} (hT : Orthogonal T)
    (hd : T = Matrix.diagonal (fun i => T i i)) (i : Fin n) :
    T i i = 1 ∨ T i i = -1 := by
  have he := congrArg (fun A : Mat n => (Aᵀ * A) i i) hd
  have hg : (Tᵀ * T) i i = 1 := by rw [hT.1]; simp
  change (Tᵀ * T) i i = _ at he
  rw [he] at hg
  have hs : T i i * T i i = 1 := by
    simpa [Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply] using hg
  have hz : (T i i - 1) * (T i i + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hz with h | h
  · left; linarith
  · right; linarith

end GS.LieAction
