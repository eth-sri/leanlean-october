
import GS.MatrixGeometry.Base



/-! Permutations act by unitary simultaneous relabeling of complex entries. -/
open Matrix GS.MatrixBase
namespace GS.MatrixFactor
variable {𝕜 : Type} [RCLike 𝕜]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def cPermMatrix (σ : Equiv.Perm ι) : Matrix ι ι 𝕜 :=
  fun i j => if i = σ j then 1 else 0

@[simp] theorem mul_cPerm_apply (A : Matrix ι ι 𝕜) (σ : Equiv.Perm ι) (i j : ι) :
    (A*cPermMatrix (𝕜 := 𝕜) σ) i j = A i (σ j) := by simp [Matrix.mul_apply, cPermMatrix]
@[simp] theorem cPerm_mul_apply (σ : Equiv.Perm ι) (A : Matrix ι ι 𝕜) (i j : ι) :
    (cPermMatrix (𝕜 := 𝕜) σ*A) i j = A (σ.symm i) j := by
  simp [Matrix.mul_apply, cPermMatrix, ← σ.symm_apply_eq]

@[simp] theorem cPerm_conjTranspose (σ : Equiv.Perm ι) :
    (cPermMatrix (𝕜 := 𝕜) σ)ᴴ = cPermMatrix  σ.symm := by aesop (add norm [cPermMatrix])

theorem cPerm_unitary (σ : Equiv.Perm ι) : Unitary (cPermMatrix (𝕜 := 𝕜) σ) := by
  constructor <;> ext i j <;>
    simp [cPerm_conjTranspose,  cPermMatrix, Matrix.one_apply]
theorem cPerm_conjugate_apply (σ : Equiv.Perm ι) (A : Matrix ι ι 𝕜) (i j : ι) :
    (cPermMatrix (𝕜 := 𝕜) σ*A*(cPermMatrix (𝕜 := 𝕜) σ)ᴴ) i j = A (σ.symm i) (σ.symm j) := by simp

theorem cPerm_trans_matrix (σ τ : Equiv.Perm ι) :
    cPermMatrix (𝕜 := 𝕜) (σ.trans τ) = cPermMatrix  τ*cPermMatrix  σ := by
  aesop

end GS.MatrixFactor
