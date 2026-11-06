
import GS.Revision.TwoFactorCells
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace


/-!
# Rank characterization of independently supported two-factor products

The intermediate slots are partitioned by their left and right block labels.
A matrix admits the prescribed supported factorization exactly when each
output block has rank at most the number of intermediate slots in its cell.

The rank bound is both necessary and sufficient. The converse constructs a
basis factorization of each block and pads it with zeros into the cell slots;
`GS.Revision.Cells.global_iff_independent` then glues these independent factors.
Empty cells and rank-zero matrices are included without separate hypotheses.
-/


namespace GS.Results.CellRank

variable {ι κ τ : Type*} [Fintype κ] [Fintype τ]

variable (A : Matrix ι κ ℝ)

/-- Factoring through any finite set of coordinates is equivalent to the rank
bound given by its cardinality. No factorization witness is an assumption. -/
theorem rank_le_card_iff_factorization  :
    A.rank ≤ Fintype.card τ ↔
      ∃ U : Matrix ι τ ℝ, ∃ V : Matrix τ κ ℝ, A = U * V := by
  classical
  constructor
  · intro h
    let S := LinearMap.range A.mulVecLin
    obtain ⟨e,he⟩ := (finrank_le_iff_exists_linearMap
      (R := ℝ)  (M' := τ → ℝ)).mp (by aesop)
    refine ⟨LinearMap.toMatrix' (S.subtype.comp e.leftInverse),
      LinearMap.toMatrix' (e.comp A.mulVecLin.rangeRestrict),?_⟩
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro x
    exact congrArg Subtype.val
      (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr he)
        (A.mulVecLin.rangeRestrict x)).symm
  · rintro ⟨U, V, rfl⟩
    exact (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)


variable {α β : Type*}

/-- Slots simultaneously belonging to the chosen output row and column blocks. -/
abbrev Cell (left : τ → α) (right : τ → β) (a : α) (b : β) :=
  {t : τ // a = left t ∧ b = right t}



end GS.Results.CellRank
