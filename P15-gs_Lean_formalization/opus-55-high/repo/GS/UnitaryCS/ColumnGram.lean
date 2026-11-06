module

public import GS.ComplexAlgebra
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

@[expose] public section


/-! # Unitary completion of matrices with real diagonal column Gram matrices

Normalized nonzero columns extend to an orthonormal basis. Zero columns are
included, so the subsequent cosine-sine theorem includes both endpoints.
The results are stated over an arbitrary `RCLike` field, covering both the
real orthogonal and the complex unitary case.
-/

noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators ComplexConjugate
namespace GS.UnitaryCS

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The unitary equations on an arbitrary finite index type. -/
def IsUnitary {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : Prop := Aᴴ * A = 1 ∧ A * Aᴴ = 1

namespace IsUnitary
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A B : Matrix ι ι 𝕜}
theorem of_conjTranspose_mul (h : Aᴴ * A = 1) : IsUnitary A :=
  ⟨h, mul_eq_one_comm.mp h⟩
theorem one : IsUnitary (1 : Matrix ι ι 𝕜) := by constructor <;> simp
theorem conjTranspose (h : IsUnitary A) : IsUnitary Aᴴ := by
  constructor <;> simp [h.1, h.2]
theorem mul (hA : IsUnitary A) (hB : IsUnitary B) : IsUnitary (A*B) := by
  constructor <;> simp [Matrix.mul_assoc, ← Matrix.mul_assoc B, ← Matrix.mul_assoc Aᴴ, hA.1, hA.2, hB.1, hB.2]
end IsUnitary

section
variable {n : ℕ} (A : Matrix (Fin n) (Fin n) 𝕜)
/-- A square matrix with real diagonal Gram matrix has a unitary
left factor, including at zero diagonal entries. -/
theorem exists_unitary_mul_diagonal (d : Fin n → ℝ)
    (hA : Aᴴ * A = diagonal (fun i => (d i : 𝕜) ^ 2)) :
    ∃ U, IsUnitary U ∧ A = U * diagonal (fun i => (d i : 𝕜)) := by
  classical
  let e₀ := EuclideanSpace.basisFun (Fin n) 𝕜
  let f := fun j => ∑ k, A k j • e₀ k
  have hcoords (i j : Fin n) : ⟪e₀ i, f j⟫_𝕜 = A i j := by
    simp [f, inner_sum, inner_smul_right, orthonormal_iff_ite.mp e₀.orthonormal]
  have hgram (i j : Fin n) : ⟪f i, f j⟫_𝕜 = if i = j then (d i : 𝕜) ^ 2 else 0 := by
    calc
      ⟪f i, f j⟫_𝕜 = ∑ k, conj (A k i) * A k j := by
        rw [← e₀.sum_inner_mul_inner (f i) (f j)]
        exact Finset.sum_congr rfl fun k _ => by rw [← inner_conj_symm (f i) (e₀ k), hcoords, hcoords]
      _ = (Aᴴ * A) i j := rfl
      _ = _ := by aesop
  let s := {i | d i ≠ 0}
  have hv : Orthonormal 𝕜 (s.restrict fun j => ((d j : 𝕜))⁻¹ • f j) := by
    rw [orthonormal_iff_ite]
    intro i j
    change ⟪((d i : 𝕜))⁻¹ • f i, ((d j : 𝕜))⁻¹ • f j⟫_𝕜 = _
    rw [inner_smul_left, inner_smul_right, hgram]
    by_cases hij : i = j
    · simp [pow_two]
      aesop
    grind
  obtain ⟨e, he⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by simp : Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin n)) = Fintype.card (Fin n))
  refine ⟨_, .of_conjTranspose_mul (mem_unitaryGroup_iff'.1 (e₀.toMatrix_orthonormalBasis_mem_unitary e)), ?_⟩
  ext i j
  simp
  by_cases hd : d j = 0
  · have hf := inner_self_eq_zero.mp ((hgram j j).trans (by grind))
    simp only [hd, RCLike.ofReal_zero, mul_zero, ← hcoords, hf, inner_zero_right]
  · simp only [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply]
    rw [he j hd]
    simp [inner_smul_right, hcoords]
    field_simp [RCLike.ofReal_ne_zero.2 hd]

/-- Ordinary square QR, including dependent input columns. -/
theorem exists_qr :
    ∃ V R : Matrix (Fin n) (Fin n) 𝕜, IsUnitary V ∧ R.BlockTriangular (fun i => i.val) ∧ A = V * R := by
  let e₀ := EuclideanSpace.basisFun (Fin n) 𝕜
  let f j := ∑ k, A k j • e₀ k
  let e := gramSchmidtOrthonormalBasis (𝕜 := 𝕜) (by simp) f
  refine ⟨_, Matrix.of fun i j => ⟪e i, f j⟫_𝕜,
    .of_conjTranspose_mul (mem_unitaryGroup_iff'.1 (e₀.toMatrix_orthonormalBasis_mem_unitary e)),
    fun i j h => gramSchmidtOrthonormalBasis_inv_triangular _ f h, ?_⟩
  ext i j
  simp only [mul_apply, Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, of_apply, e.sum_inner_mul_inner]
  simp [f, inner_sum, inner_smul_right, orthonormal_iff_ite.1 e₀.orthonormal]

end

end GS.UnitaryCS
