module

public import GS.Results.CellRank

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Block-rank criterion for the original two-factor matrix class

`inA2_iff_block_rank` is stated for the actual matrices and permutation in
`GS.InA2`. Its blocks are represented as matrices with zeros outside the
selected row and column blocks. Thus no choice of local row/column numbering
is needed, and unequal final blocks or empty intermediate cells cause no
exception. The criterion includes singular factors and singular outputs.
-/

noncomputable section
open Matrix

namespace GS.Results.OriginalCellRank

section Coordinates

variable {α β ι κ τ : Type*}
variable [DecidableEq α] [DecidableEq β] [Fintype ι] [Fintype κ] [Fintype τ]

/-- Add explicit block labels to the row and column coordinates, with zero
entries on every copy whose label disagrees with the original coordinate. -/
def labelledMatrix (row : ι → α) (col : κ → β) (A : Matrix ι κ ℝ) :
    Matrix (α × ι) (β × κ) ℝ :=
  fun ai bj => if ai.1 = row ai.2 ∧ bj.1 = col bj.2 then A ai.2 bj.2 else 0

section
variable (row : ι → α) (col : κ → β) (left : τ → α) (right : τ → β) (A : Matrix ι κ ℝ)
/-- A factorization of the original matrix with prescribed coordinate support. -/
def CoordinateFactorable : Prop :=
  ∃ L : Matrix ι τ ℝ, ∃ R : Matrix τ κ ℝ,
    (∀ i t, row i ≠ left t → L i t = 0) ∧
    (∀ t j, col j ≠ right t → R t j = 0) ∧ A = L * R

theorem coordinate_iff_labelled :
    CoordinateFactorable row col left right A ↔
      Revision.Cells.GloballyFactorable left right (labelledMatrix row col A) := by
  classical
  constructor
  · rintro ⟨L, R, hL, hR, hA⟩
    let L' : Matrix (α × ι) τ ℝ := fun ai t =>
      if ai.1 = row ai.2 then L ai.2 t else 0
    let R' : Matrix τ (β × κ) ℝ := fun t bj =>
      if bj.1 = col bj.2 then R t bj.2 else 0
    refine ⟨L', R', fun a i t h => by grind, fun t b j h => by grind, ?_⟩
    ext ⟨a, i⟩ ⟨b, j⟩
    by_cases ha : a = row i <;> by_cases hb : b = col j <;>
      simp [labelledMatrix, L', R', ha, hb, hA, Matrix.mul_apply]
  · rintro ⟨L', R', hL', hR', hA⟩
    refine ⟨fun i t => L' (row i, i) t, fun t j => R' t (col j, j), fun i t h => hL' _ _ _ h, fun t j h => hR' _ _ _ h, ?_⟩
    ext i j
    simpa [labelledMatrix, Matrix.mul_apply] using congrArg (fun B => B (row i, i) (col j, j)) hA

/-- A support factorization exists exactly when every zero-padded output
block has rank at most the number of available intermediate slots. -/
theorem coordinate_iff_block_rank :
    CoordinateFactorable row col left right A ↔
      ∀ a b, (Matrix.of fun i j => if a = row i ∧ b = col j then A i j else 0).rank ≤
        Fintype.card (CellRank.Cell left right a b) := by
  rw [coordinate_iff_labelled, CellRank.global_iff_block_rank]
  rfl

end

end Coordinates

section
variable {n : ℕ} (b₁ b₂ : ℕ) (σ : Equiv.Perm (Fin n))
theorem inA2_iff_coordinate (A : Mat n) :
    InA2 b₁ b₂ (permMatrix σ) A ↔
      CoordinateFactorable (fun i : Fin n => i.val / b₂)
        (fun j : Fin n => j.val / b₁)
        (fun t : Fin n => (σ t).val / b₂)
        (fun t : Fin n => t.val / b₁) A := by
  constructor
  · rintro ⟨B₁, B₂, hb₁, hb₂, hA⟩
    refine ⟨B₂ * permMatrix σ, B₁, ?_, ?_, hA⟩
    · aesop
    aesop
  · rintro ⟨L, R, hL, hR, hA⟩
    refine ⟨R, L * (permMatrix σ)ᵀ, ?_, ?_, ?_⟩
    · tauto
    · intro i j h
      simp_all
    · simpa only [product2, Matrix.mul_assoc, (perm_orthogonal σ).1,
        Matrix.one_mul] using hA

end

end GS.Results.OriginalCellRank
