import Mathlib.Tactic

import GS.Results.CellRank




/-!
# Block-rank criterion for the original two-factor matrix class

`inA2_iff_block_rank` is stated for the actual matrices and permutation in
`GS.InA2`. Its blocks are represented as matrices with zeros outside the
selected row and column blocks. Thus no choice of local row/column numbering
is needed, and unequal final blocks or empty intermediate cells cause no
exception. The criterion includes singular factors and singular outputs.
-/


namespace GS.Results.OriginalCellRank

section Coordinates

variable {α β ι κ τ : Type*}
variable [DecidableEq α] [DecidableEq β] [Fintype ι] [Fintype κ] [Fintype τ]

variable (row : ι → α)

/-- A factorization of the original matrix with prescribed coordinate support. -/
def CoordinateFactorable  (col : κ → β)
    (left : τ → α) (right : τ → β) (A : Matrix ι κ ℝ) : Prop :=
  ∃ L : Matrix ι τ ℝ, ∃ R : Matrix τ κ ℝ,
    (∀ i t, row i ≠ left t → L i t = 0) ∧
    (∀ t j, col j ≠ right t → R t j = 0) ∧ A = L * R

/-- A support factorization exists exactly when every zero-padded output
block has rank at most the number of available intermediate slots. -/
theorem coordinate_iff_block_rank  (col : κ → β)
    (left : τ → α) (right : τ → β) (A : Matrix ι κ ℝ) :
    CoordinateFactorable row col left right A ↔
      ∀ a b, (Matrix.of fun i j => if a = row i ∧ b = col j then A i j else 0).rank ≤
        Fintype.card (CellRank.Cell left right a b) := by

  constructor
  · rintro ⟨L,R,hL,hR,hA⟩ a b
    apply (CellRank.rank_le_card_iff_factorization (τ := CellRank.Cell left right a b) _).mpr
    refine ⟨(fun i t => L i t.val),(fun t j => R t.val j),?_⟩
    ext i j
    calc
      _ = ∑ t, if a = row i ∧ b = col j then L i t * R t j else 0 := by aesop
      _ = _ := by
        change _ = ∑ t : CellRank.Cell left right a b, L i t.val * R t.val j
        rw [← Finset.sum_subtype (Finset.univ.filter fun t => a = left t ∧ b = right t)
          (by simp) (fun t => L i t * R t j), Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro t _
        by_cases hi : row i = left t <;> by_cases hj : col j = right t <;> simp_all
  · intro h
    choose U V hUV using fun a b =>
      (CellRank.rank_le_card_iff_factorization (τ := CellRank.Cell left right a b) _).mp (h a b)
    let L : Matrix ι τ ℝ := fun i t =>
      if ht : row i = left t then U (row i) (right t) i ⟨t,ht,rfl⟩ else 0
    let R : Matrix τ κ ℝ := fun t j =>
      if ht : col j = right t then V (left t) (col j) ⟨t,rfl,ht⟩ j else 0
    refine ⟨L,R,?_,?_,?_⟩
    · aesop
    · aesop
    · ext i j
      have he := congrFun (congrFun (hUV (row i) (col j)) i) j
      simp only [Matrix.of_apply, and_self, ite_true, Matrix.mul_apply] at he
      rw [he]
      simp only [Matrix.mul_apply]
      apply Fintype.sum_of_injective (fun t : CellRank.Cell left right (row i) (col j) => t.val) Subtype.val_injective
      · intro t ht
        by_cases hi : row i = left t <;> by_cases hj : col j = right t
        · aesop
        all_goals aesop
      · rintro ⟨t,hi,hj⟩
        simp only [L,R,dif_pos hi,dif_pos hj]
        generalize row i = a at *
        generalize col j = b at *
        cases hi
        cases hj
        rfl


end Coordinates

end GS.Results.OriginalCellRank
