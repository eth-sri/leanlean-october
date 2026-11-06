module

public import GS.Revision.TwoFactorCells
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

set_option backward.isDefEq.respectTransparency false

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

noncomputable section

namespace GS.Results.CellRank

variable {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]

/-- Factoring through any finite set of coordinates is equivalent to the rank
bound given by its cardinality. No factorization witness is an assumption. -/
theorem rank_le_card_iff_factorization (A : Matrix ι κ ℝ) :
    A.rank ≤ Fintype.card τ ↔
      ∃ U : Matrix ι τ ℝ, ∃ V : Matrix τ κ ℝ, A = U * V := by
  classical
  refine ⟨fun h => ?_, fun ⟨U, V, h⟩ => h ▸ (Matrix.rank_mul_le_left U V).trans (Matrix.rank_le_card_width U)⟩
  let S : Submodule ℝ (ι → ℝ) := LinearMap.range A.mulVecLin
  let b : Module.Basis (Fin A.rank) ℝ S := Module.finBasis ℝ S
  let x : κ → S := fun j => A.mulVecLin.rangeRestrict (Pi.single j 1)
  let e : Fin A.rank → τ := fun k => (Fintype.equivFin τ).symm (Fin.castLE h k)
  have he : Function.Injective e :=
    (Fintype.equivFin τ).symm.injective.comp (Fin.castLE_injective h)
  refine ⟨fun i => Function.extend e (fun k => (b k : ι → ℝ) i) 0,
    fun t j => Function.extend e (fun k => b.repr (x j) k) 0 t, ?_⟩
  ext i j
  have h := congrArg (fun y : S => (y : ι → ℝ) i) (b.sum_repr (x j))
  rw [Matrix.mul_apply, ← Fintype.sum_of_injective e he _ _ (by aesop) (by aesop)]
  simpa only [x, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Matrix.mulVecLin_apply,
    LinearMap.rangeRestrict, LinearMap.codRestrict_apply, Matrix.mulVec_single_one, Matrix.col_apply, mul_comm] using h.symm

section Cells

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

section
variable (left : τ → α) (right : τ → β) (a : α) (b : β)
/-- Slots simultaneously belonging to the chosen output row and column blocks. -/
abbrev Cell :=
  {t : τ // a = left t ∧ b = right t}

private theorem cellSum_eq_product
    (U : Matrix ι τ ℝ) (V : Matrix τ κ ℝ) :
    Revision.Cells.cellSum left right a b U V =
      Matrix.of (fun i (t : Cell left right a b) => U i t.val) *
        Matrix.of (fun (t : Cell left right a b) j => V t.val j) := by
  classical
  ext i j
  symm
  apply Fintype.sum_of_injective (Subtype.val : Cell left right a b → τ)
    Subtype.val_injective
  · simp_all
  simp_all

/-- A single cell has independent outer-product witnesses exactly when the
corresponding block satisfies its numerical rank bound. -/
theorem cell_factorization_iff_rank
    (B : Matrix ι κ ℝ) :
    (∃ U : Matrix ι τ ℝ, ∃ V : Matrix τ κ ℝ,
      B = Revision.Cells.cellSum left right a b U V) ↔
      B.rank ≤ Fintype.card (Cell left right a b) := by
  classical
  rw [rank_le_card_iff_factorization]
  constructor
  · rintro ⟨U, V, hB⟩
    exact ⟨_, _, hB.trans (cellSum_eq_product left right a b U V)⟩
  · rintro ⟨U, V, rfl⟩
    refine ⟨fun i t => if ht : a = left t ∧ b = right t then U i ⟨t, ht⟩ else 0,
      fun t j => if ht : a = left t ∧ b = right t then V ⟨t, ht⟩ j else 0, ?_⟩
    rw [cellSum_eq_product]
    congr <;> aesop

end

/-- Complete block-rank characterization of the global supported two-factor
class. Each block rank is bounded by the number of its intermediate slots. -/
theorem global_iff_block_rank
    (left : τ → α) (right : τ → β)
    (A : Matrix (α × ι) (β × κ) ℝ) :
    Revision.Cells.GloballyFactorable left right A ↔
      ∀ a b, (Matrix.of fun i j => A (a, i) (b, j)).rank ≤
        Fintype.card (Cell left right a b) := by
  rw [Revision.Cells.global_iff_independent]
  exact forall₂_congr fun a b => by rw [← cell_factorization_iff_rank]; simp [← Matrix.ext_iff]

end Cells

end GS.Results.CellRank
