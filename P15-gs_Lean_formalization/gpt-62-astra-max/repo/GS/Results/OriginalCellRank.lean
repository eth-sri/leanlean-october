module

public import GS.Results.CellRank

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

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
open scoped BigOperators

namespace GS.Results.OriginalCellRank
open Isometric

variable {α β ι κ τ : Type*} [DecidableEq α] [DecidableEq β] [Fintype ι] [Fintype κ] [Fintype τ]

/-- Sum over the linking slots, extending by zero off the cell. -/
private lemma extend_sum {p : τ → Prop} [DecidablePred p] {f : Subtype p → ℝ} {g : τ → ℝ}
    (inside : ∀ t, f t = g t.val) (outside : ∀ t, ¬p t → g t = 0) : ∑ t, f t = ∑ t, g t := by
  rw [← Fintype.sum_subtype_add_sum_subtype p g,show (∑ t : {t // ¬p t}, g t.val) = 0 from Finset.sum_eq_zero fun t _ => outside _ t.property,add_zero]
  exact Finset.sum_congr rfl fun t _ => inside t

/-- A support factorization exists exactly when every zero-padded output
block has rank at most the number of available intermediate slots. -/
theorem coordinate_iff_block_rank (row : ι → α) (col : κ → β)
    (left : τ → α) (right : τ → β) (A : Matrix ι κ ℝ) :
    (∃ (L : Matrix ι τ ℝ) (R : Matrix τ κ ℝ), (∀ i t, row i ≠ left t → L i t = 0) ∧
      (∀ t j, col j ≠ right t → R t j = 0) ∧ A = L*R) ↔
    ∀ a b, (Matrix.of fun i j => if a = row i ∧ b = col j then A i j else 0).rank ≤
        Fintype.card {t // a = left t ∧ b = right t} := by
  classical
  simp_rw [CellRank.rank_le_card_iff_factorization]
  let slots a b := {t // a = left t ∧ b = right t}
  constructor
  · rintro ⟨L,R,hL,hR,rfl⟩ a b
    refine ⟨L.submatrix id Subtype.val, R.submatrix Subtype.val id, ?_⟩
    ext i j
    simp only [of_apply, mul_apply, submatrix_apply, id_eq]
    split_ifs with h
    · exact (extend_sum (p := fun t => a = left t ∧ b = right t) (fun _ => rfl) (by grind)).symm
    · symm; apply Finset.sum_eq_zero
      rintro ⟨t,ht⟩ _; grind
  · intro h
    choose U V eq using h
    let L : Matrix ι τ ℝ := fun i t => if row i = left t then U _ _ i ⟨t,rfl,rfl⟩ else 0
    let R : Matrix τ κ ℝ := fun t j => if col j = right t then V _ _ ⟨t,rfl,rfl⟩ j else 0
    refine ⟨L,R,by simp_all [L],by simp_all [R],?_⟩
    ext i j
    have hij := congrFun (congrFun (eq (row i) (col j)) i) j
    simp only [of_apply, and_self, ite_true] at hij
    refine hij.trans ?_
    apply extend_sum (p := fun t => row i = left t ∧ col j = right t)
    · have same a b (s : slots a b) : U a b i s * V a b s j = U _ _ i ⟨s.val,rfl,rfl⟩ * V _ _ ⟨s.val,rfl,rfl⟩ j := by rcases s with ⟨t,rfl,rfl⟩; rfl
      exact fun t => by simpa [L,R,t.property.1,t.property.2] using same _ _ t
    · dsimp [L,R]; grind

end GS.Results.OriginalCellRank

namespace GSPalomar
open GS GS.Isometric

/-- Exact cell-rank criterion, including singular matrices and empty cells. -/
theorem two_factor_rank_criterion {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 b₁ b₂ (GS.permMatrix σ) A ↔
      ∀ a b : ℕ,
        (Matrix.of fun i j : Fin n =>
          if a = i.val / b₂ ∧ b = j.val / b₁ then A i j else 0).rank ≤
        Fintype.card {t : Fin n // a = (σ t).val / b₂ ∧ b = t.val / b₁} := by
  rw [← GS.Results.OriginalCellRank.coordinate_iff_block_rank (left := fun t => (σ t).val / b₂) (right := fun t : Fin n => t.val / b₁)]
  constructor
  · rintro ⟨B₁, B₂, hb₁, hb₂, hA⟩
    refine ⟨B₂ * permMatrix σ, B₁, ?_, ?_, hA⟩
    · intro i t h; change (B₂ * perm ℝ σ) i t = 0; simpa using hb₂ i (σ t) h
    solve_by_elim
  · rintro ⟨L, R, hL, hR, hA⟩
    refine ⟨R, L * (perm ℝ σ)ᴴ, ?_, ?_, ?_⟩
    · solve_by_elim
    · intro i j h
      change (L * (perm ℝ σ)ᴴ) i j = 0
      simp only [perm_star,mul_perm_apply]; apply hL; simpa using h
    · change A = L * (perm ℝ σ)ᴴ * perm ℝ σ * R; simpa only [Matrix.mul_assoc,(perm_isU (𝕜 := ℝ) σ).star_cancel] using hA

end GSPalomar
