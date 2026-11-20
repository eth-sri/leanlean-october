module

public import GS.Shared.Basic

public import Mathlib.LinearAlgebra.Matrix.Permutation

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open Matrix Equiv
open scoped BigOperators

namespace GS.Shared
def permMatrix {𝕜 ι : Type*} [DecidableEq ι] [Zero 𝕜] [One 𝕜] (σ : Equiv.Perm ι) : Matrix ι ι 𝕜 :=
  fun i j => if i = σ j then 1 else 0

variable {𝕜 ι : Type*} [DecidableEq ι]

theorem perm_eq [Zero 𝕜] [One 𝕜] (σ : Equiv.Perm ι) :
    permMatrix (𝕜 := 𝕜) σ = Equiv.Perm.permMatrix 𝕜 (σ.symm : Perm ι) := by
  ext i j
  simp [permMatrix, Equiv.symm_apply_eq]

variable [RCLike 𝕜]

@[simp] theorem perm_conjTranspose (σ : Perm ι) :
    (permMatrix (𝕜 := 𝕜) σ)ᴴ = permMatrix σ.symm := by
  simp only [perm_eq, Matrix.conjTranspose_permMatrix, Equiv.Perm.inv_def]

@[simp] theorem perm_refl : permMatrix (𝕜 := 𝕜) (Equiv.refl ι) = 1 := by
  simp [perm_eq]

variable [Fintype ι]

@[simp] theorem mul_perm_apply (A : Matrix ι ι 𝕜) (σ : Perm ι) (i j : ι) :
    (A * permMatrix (𝕜 := 𝕜) σ) i j = A i (σ j) := by
  simp [perm_eq, PEquiv.mul_toMatrix_toPEquiv]

@[simp] theorem perm_mul_apply (σ : Perm ι) (A : Matrix ι ι 𝕜) (i j : ι) :
    (permMatrix (𝕜 := 𝕜) σ * A) i j = A (σ.symm i) j := by
  simp [perm_eq, PEquiv.toMatrix_toPEquiv_mul]

theorem perm_unitary (σ : Perm ι) : Unitary (permMatrix (𝕜 := 𝕜) σ) := by
  constructor <;> simp only [perm_eq, Matrix.conjTranspose_permMatrix, ← Matrix.permMatrix_mul,
    mul_inv_cancel, inv_mul_cancel, Matrix.permMatrix_one]

variable {n : ℕ}

theorem perm_conjugate_apply (σ : Equiv.Perm (Fin n)) (A : M 𝕜 n) (i j : Fin n) :
    (permMatrix (𝕜 := 𝕜) σ*A*(permMatrix (𝕜 := 𝕜) σ)ᴴ) i j = A (σ.symm i) (σ.symm j) := by simp

end GS.Shared
