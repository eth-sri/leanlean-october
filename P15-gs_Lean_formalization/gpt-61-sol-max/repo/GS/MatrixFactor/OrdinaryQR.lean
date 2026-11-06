
import GS.MatrixGeometry.Base
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho



/-!
# Ordinary complex QR and the unitary triangular obstruction

The QR construction uses a completed orthonormal basis of the genuine complex
Euclidean space. It applies to singular matrices as well. No phase or positive
diagonal convention is imposed on the triangular factor.
-/

open Matrix GS.MatrixBase InnerProductSpace

namespace GS.MatrixFactor
variable {𝕜 : Type} [RCLike 𝕜]

variable (A : KMat 𝕜 n)

def CUpper  : Prop := A.BlockTriangular (fun i => i.val)

theorem cSupported_blockTriangular {block : Fin n → ℕ} {A : KMat 𝕜 n}
    (h : CSupported block A) : A.BlockTriangular block := by
  intro i j hij
  exact h i j (Ne.symm (Nat.ne_of_lt hij))



theorem cUpper_blockTriangular {b : ℕ} {A : KMat 𝕜 n} (h : CUpper A) :
    A.BlockTriangular (fun i : Fin n => i.val / b) :=
by
  intro i j hij
  apply h
  by_contra hn
  exact (not_lt_of_ge (Nat.div_le_div_right (Nat.le_of_not_gt hn))) hij

/-- A unitary matrix upper triangular in block labels is block diagonal. -/
theorem unitary_blockTriangular_supported {block : Fin n → ℕ} {U : KMat 𝕜 n}
    (hU : Unitary U) (htri : U.BlockTriangular block) : CSupported block U := by
  letI : Invertible U :=
    { invOf := Uᴴ, invOf_mul_self := hU.1, mul_invOf_self := hU.2 }
  have hi :=
    Matrix.blockTriangular_inv_of_blockTriangular htri
  rw [Matrix.inv_eq_left_inv hU.1] at hi
  intro i j hij
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hz := hi   hlt
    simpa only [Matrix.conjTranspose_apply, star_eq_zero] using hz
  · exact htri hgt

/-- Inversion preserves arbitrary block support for invertible complex matrices. -/
theorem cSupported_inverse {block : Fin n → ℕ} {A : KMat 𝕜 n}
    (hA : CSupported block A) [Invertible A] : CSupported block A⁻¹ := by
  have h₁ : A.BlockTriangular block := fun _ _ h => hA _ _ (ne_of_gt h)
  have h₂ : A.BlockTriangular (fun i => OrderDual.toDual (block i)) :=
    fun _ _ h => hA _ _ (ne_of_lt h)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact Matrix.blockTriangular_inv_of_blockTriangular h₂ h
  · exact Matrix.blockTriangular_inv_of_blockTriangular h₁ h

theorem unitary_det_ne_zero {Q : KMat 𝕜 n} (hQ : Unitary Q) : Q.det ≠ 0 :=
  Matrix.det_ne_zero_of_left_inverse hQ.1

/-- Ordinary complex square QR, including dependent input columns. -/
theorem exists_ordinary_qr  :
    ∃ V R : KMat 𝕜 n, Unitary V ∧ CUpper R ∧ A=V*R := by
  let e₀ :=
    EuclideanSpace.basisFun (Fin n) 𝕜
  let f : Fin n → EuclideanSpace 𝕜 (Fin n) :=
    fun j => WithLp.toLp 2 (fun i => A i j)
  have hdim : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = Fintype.card (Fin n) := by
    simp
  let e := gramSchmidtOrthonormalBasis hdim f
  let V := e₀.toBasis.toMatrix e
  let R : KMat 𝕜 n := fun i j => ⟪e i, f j⟫_𝕜
  have ho := e₀.toMatrix_orthonormalBasis_mem_unitary e
  have ht : CUpper R := by
    intro i j hij
    exact gramSchmidtOrthonormalBasis_inv_triangular hdim f hij
  refine ⟨V,R,ho,ht,?_⟩
  ext i j
  change A i j = ∑ k, V i k * R k j
  simp only [V, R, Module.Basis.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  simpa only [e₀, EuclideanSpace.basisFun_inner, f] using
    (e.sum_inner_mul_inner (e₀ i) (f j)).symm

end GS.MatrixFactor
