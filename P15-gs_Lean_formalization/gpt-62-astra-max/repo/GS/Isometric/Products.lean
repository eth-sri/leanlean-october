module

public import GS.Isometric.Matrix

@[expose] public section

/-! The column convention for permutation matrices, over either field. -/
noncomputable section
open Matrix
namespace GS.Isometric
variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Matrix ι ι 𝕜}
lemma IsU.star_cancel (h : IsU A) (B : Matrix ι ι 𝕜) : Aᴴ*(A*B) = B := by grind
lemma IsU.cancel_star (h : IsU A) (B : Matrix ι ι 𝕜) : A*(Aᴴ*B) = B := by grind

def perm (𝕜 : Type*) [RCLike 𝕜] (σ : Equiv.Perm ι) : Matrix ι ι 𝕜 := fun i j => if i = σ j then 1 else 0

@[simp] lemma mul_perm_apply (A : Matrix ι ι 𝕜) (σ : Equiv.Perm ι) (i j) :
    (A * perm 𝕜 σ) i j = A i (σ j) := by simp [mul_apply,perm]
@[simp] lemma perm_mul_apply (A : Matrix ι ι 𝕜) (σ : Equiv.Perm ι) (i j) :
    (perm 𝕜 σ * A) i j = A (σ.symm i) j := by simp [mul_apply,perm,← σ.symm_apply_eq]
@[simp] lemma perm_star (σ : Equiv.Perm ι) : (perm 𝕜 σ)ᴴ = perm 𝕜 σ.symm := by
  ext i j; simp [perm,conjTranspose_apply,← σ.symm_apply_eq,eq_comm]
@[simp] lemma perm_id : perm 𝕜 (Equiv.refl ι) = 1 := by ext i j; rfl
lemma perm_isU (σ : Equiv.Perm ι) : IsU (perm 𝕜 σ) := by
  apply IsU.of_left
  ext; simp [perm_star,perm_mul_apply,perm,one_apply]
end GS.Isometric
