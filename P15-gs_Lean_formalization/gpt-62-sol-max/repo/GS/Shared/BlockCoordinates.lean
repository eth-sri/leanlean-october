module

public import GS.Shared.Factorization

public import Mathlib.Data.Matrix.Composition

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix
namespace GS.Shared

variable {𝕜 : Type*} [RCLike 𝕜] {k b n s : ℕ}

/-- Reindex a matrix of square blocks by a scalar coordinate system. -/
def blockFlatten (e : Fin k × Fin b ≃ Fin n) : Matrix (Fin k) (Fin k) (M 𝕜 b) ≃+* M 𝕜 n :=
  (Matrix.compRingEquiv (Fin k) (Fin b) 𝕜).trans (Matrix.reindexRingEquiv 𝕜 e)

abbrev blockView (e : Fin k × Fin b ≃ Fin n) := (blockFlatten (𝕜 := 𝕜) e).symm

@[simp] theorem blockView_apply (e : Fin k × Fin b ≃ Fin n) (A : M 𝕜 n) (i j : Fin k) (a b : Fin b) :
    blockView e A i j a b = A (e (i,a)) (e (j,b)) := rfl

@[simp] theorem blockView_conjTranspose (e : Fin k × Fin b ≃ Fin n) (A : M 𝕜 n) :
    blockView e Aᴴ = (blockView e A)ᴴ := by
  rfl

def packBlocks (e : Fin k × Fin b ≃ Fin n) (D : Fin k → M 𝕜 b) : M 𝕜 n :=
  blockFlatten e (diagonal D)

@[simp] theorem packBlocks_apply (e : Fin k × Fin b ≃ Fin n) (D : Fin k → M 𝕜 b) (i j : Fin n) :
    packBlocks e D i j = if (e.symm i).1 = (e.symm j).1 then D (e.symm i).1 (e.symm i).2 (e.symm j).2 else 0 := by
  change diagonal D (e.symm i).1 (e.symm j).1 (e.symm i).2 (e.symm j).2 = _
  aesop

theorem standard_block_label (x : Fin k × Fin b) : (finProdFinEquiv x).val / b = x.1.val := by
  change (x.2.val + b * x.1.val) / b = x.1.val
  grind [Nat.add_mul_div_left, Nat.zero_lt_of_lt, Nat.div_eq_of_lt, zero_add]

@[simp] theorem blockView_pack (e : Fin k × Fin b ≃ Fin n) (D : Fin k → M 𝕜 b) :
    blockView e (packBlocks e D) = diagonal D := (blockFlatten e).symm_apply_apply _

/-- In a conforming scalar index system a supported matrix has diagonal block view. -/
theorem blockView_diagonal (e : Fin k × Fin b ≃ Fin n) (he : ∀ x, (e x).val / s = x.1.val)
    {A : M 𝕜 n} (hA : BlockDiagonal s A) :
    blockView e A = diagonal (fun i => blockView e A i i) := by
  ext i j a b
  by_cases h : i = j
  · subst j; simp
  · rw [diagonal_apply_ne _ h, Matrix.zero_apply, blockView_apply]
    apply hA
    grind

theorem packBlocks_supported (e : Fin k × Fin b ≃ Fin n) (he : ∀ x, (e x).val / s = x.1.val)
    (D : Fin k → M 𝕜 b) : BlockDiagonal s (packBlocks e D) := by
  intro i j hij
  obtain ⟨x,rfl⟩ := e.surjective i
  obtain ⟨y,rfl⟩ := e.surjective j
  aesop

theorem packBlocks_unitary_iff (e : Fin k × Fin b ≃ Fin n) (D : Fin k → M 𝕜 b) :
    Unitary (packBlocks e D) ↔ ∀ i, Unitary (D i) := by
  have eq (A B : M 𝕜 n) : A = B ↔ blockView e A = blockView e B :=
    (blockView e).injective.eq_iff.symm
  rw [Unitary, eq, eq, map_one]
  simp only [map_mul, blockView_conjTranspose, blockView_pack,
    diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one,
    diagonal_injective.eq_iff, funext_iff, ← forall_and]
  rfl

theorem supported_blocks_iff (e : Fin k × Fin b ≃ Fin n) (he : ∀ x, (e x).val / s = x.1.val)
    (A : M 𝕜 n) : (BlockDiagonal s A ∧ Unitary A) ↔
      ∃ D : Fin k → M 𝕜 b, (∀ i, Unitary (D i)) ∧ A = packBlocks e D := by
  constructor
  · rintro ⟨hs,hu⟩
    let D i := blockView e A i i
    have h : A = packBlocks e D := (blockFlatten e).symm.injective
      ((blockView_diagonal e he hs).trans ((blockFlatten e).symm_apply_apply _).symm)
    grind [packBlocks_unitary_iff]
  grind [packBlocks_supported, packBlocks_unitary_iff]

theorem blockView_pack_sandwich (e : Fin k × Fin b ≃ Fin n) (U V : Fin k → M 𝕜 b)
    (C : M 𝕜 n) (i j : Fin k) :
    blockView e (packBlocks e U * C * packBlocks e V) i j = U i * blockView e C i j * V j := by
  simp

theorem blockView_sandwich (e : Fin k × Fin b ≃ Fin n) (he : ∀ x, (e x).val / s = x.1.val)
    {A C B : M 𝕜 n} (hA : BlockDiagonal s A) (hB : BlockDiagonal s B) (i j : Fin k) :
    blockView e (A*C*B) i j = blockView e A i i * blockView e C i j * blockView e B j j := by
  conv_lhs =>
    rw [map_mul, map_mul, blockView_diagonal e he hA, blockView_diagonal e he hB,
      Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem blockView_unitary (e : Fin k × Fin b ≃ Fin n) (he : ∀ x, (e x).val / s = x.1.val)
    {A : M 𝕜 n} (hA : BlockDiagonal s A) (hu : Unitary A) (i : Fin k) :
    Unitary (blockView e A i i) := by
  obtain ⟨D,hD,rfl⟩ := (supported_blocks_iff e he A).mp ⟨hA,hu⟩
  simpa using hD i

end GS.Shared
