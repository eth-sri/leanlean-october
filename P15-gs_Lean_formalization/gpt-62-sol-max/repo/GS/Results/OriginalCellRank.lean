module

public import GS.Shared.Permutation

public import GS.RankFactorization

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix
open scoped BigOperators

namespace GS.Results.OriginalCellRank

private theorem sum_slots {τ : Type*} [Fintype τ] {p : τ → Prop} [DecidablePred p]
    (f : Subtype p → ℝ) : ∑ t, f t = ∑ t, if h : p t then f ⟨t,h⟩ else 0 := by
  apply Fintype.sum_of_injective Subtype.val Subtype.val_injective <;> aesop

/-- Exact rank criterion for `GS.InA2`, with its actual permutation and original
coordinates. There are no factorization hypotheses on the right-hand side. -/
theorem _root_.GSPalomar.two_factor_rank_criterion {n : ℕ} (b₁ b₂ : ℕ)
    (σ : Equiv.Perm (Fin n)) (A : GS.Mat n) :
    GS.InA2 b₁ b₂ (GS.permMatrix σ) A ↔
      ∀ a b : ℕ,
        (Matrix.of fun i j : Fin n =>
          if a = i.val / b₂ ∧ b = j.val / b₁ then A i j else 0).rank ≤
        Fintype.card {t : Fin n // a = (σ t).val / b₂ ∧ b = t.val / b₁} := by
  classical
  let row (i : Fin n) := i.val / b₂
  let col (j : Fin n) := j.val / b₁
  let left := row ∘ σ
  let Cell a b := {t : Fin n // a = left t ∧ b = col t}
  let B a b : Mat n := Matrix.of fun i j => if a = row i ∧ b = col j then A i j else 0
  let P := Shared.permMatrix (𝕜 := ℝ) σ
  change InA2 b₁ b₂ P A ↔ ∀ a b, (B a b).rank ≤ Fintype.card (Cell a b)
  constructor
  · rintro ⟨R,L,hR,hL,hA⟩ a b
    let K := L*P
    have hK (i t : Fin n) (h : row i ≠ left t) : K i t = 0 := by
      simpa [K,P] using hL i (σ t) h
    change A = K*R at hA
    change (∀ t j, col t ≠ col j → R t j = 0) at hR
    refine (rank_le_card_iff_factorization (B a b)).mpr
      ⟨K.submatrix id Subtype.val, R.submatrix Subtype.val id, ?_⟩
    ext i j
    simp only [B, Matrix.of_apply, hA, Matrix.mul_apply, Matrix.submatrix_apply, id_eq,
      Finset.ite_sum_zero]
    change _ = ∑ t : {t : Fin n // a = left t ∧ b = col t}, K i t * R t j
    rw [sum_slots]
    grind
  · intro h
    choose U V hUV using fun a b => (rank_le_card_iff_factorization (B a b)).mp (h a b)
    let L : Mat n := fun i t => if row i = left t then U (left t) (col t) i ⟨t,rfl,rfl⟩ else 0
    let R : Mat n := fun t j => if col j = col t then V (left t) (col t) ⟨t,rfl,rfl⟩ j else 0
    let L' : Mat n := fun i j => L i (σ.symm j)
    refine ⟨R,L',?_,?_,?_⟩
    · intro; grind
    · intro; grind
    · rw [product2, show L' * P = L by ext; simp [P,L']]
      ext i j
      have hh := congrFun (congrFun (hUV (row i) (col j)) i) j
      simp only [B, Matrix.of_apply, and_self, ite_true, Matrix.mul_apply] at hh
      rw [hh, Matrix.mul_apply, sum_slots]
      apply Finset.sum_congr rfl
      intro t _
      simp only [L,R]
      generalize row i = a
      grind

end GS.Results.OriginalCellRank
