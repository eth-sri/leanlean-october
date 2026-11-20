module

/-
Upstream source and modification notice
Modified from OpenAI's matrix-multiplication sources to support arbitrary fields.
See UPSTREAM.md for provenance and changes; Apache-2.0 license retained in LICENSE.
-/

public import OAI.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Integral.Degeneration

@[expose] public noncomputable section

namespace OAI.MatrixMultiplication.AuxiliarySeparation
open Foundation
section
variable {K : Type*} [CommSemiring K]

/-- Use predecessor indices throughout: the product of polynomials of
degrees at most `a` and `b` has degree at most `a+b`. -/
def shift {a b : ℕ} (i : Fin (a+1)) (j : Fin (b+1)) : Fin (a+b+1) := ⟨i.val+j.val, by omega⟩

def convolution (a b : ℕ) : Tensor K (Fin (a+1)) (Fin (b+1)) (Fin (a+b+1)) :=
  fun i j k => if shift i j = k then 1 else 0

end

namespace Price
open Polynomial Foundation
open scoped Polynomial

variable {K : Type*} [CommRing K]

/-- Use a formal indeterminate for the interpolation nodes. The Vandermonde
adjugate gives a polynomial restriction, and the determinant on the target
is monic even over the integers. -/
theorem value_convolution_le (χ : Price K) (a b : ℕ) :
    χ.value (convolution (K := K) a b) ≤ χ.eval (TensorResource.scalars (a+b+1)) := by
  classical
  let h := a+b+1
  let v (i : Fin h) := (X ^ i.val : K[X])
  let V := Matrix.vandermonde v
  have hm : V.det.Monic := by
    rw [Matrix.det_vandermonde]
    refine monic_prod_of_monic _ _ fun i _ => monic_prod_of_monic _ _ fun j hj => monic_X_pow_sub ?_
    exact (degree_X_pow_le _).trans_lt (by exact_mod_cast (show i.val < j.val from (Finset.mem_Ioi.mp hj : i < j)))
  rw [← χ.value_scalarTensor h]
  let ev {n} (i : Fin n) (r : Fin h) := v r ^ i.val
  apply χ.value_top _ _ ev ev V.adjugate V.det.natDegree
  intro i j z
  have he := congrFun (congrFun (Matrix.adjugate_mul V) z) (shift i j)
  simp [Tensor.restrict, scalarTensor, apply_ite, ite_and, ev, ← pow_add, -finsetSum_coeff]
  simp [V, Matrix.mul_apply, Matrix.one_apply, shift, Fin.ext_iff, mul_comm, eq_comm] at he
  rw [← he]
  split_ifs <;> simp [V, hm.coeff_natDegree, convolution, shift, Fin.ext_iff, eq_comm, *]

end Price

end OAI.MatrixMultiplication.AuxiliarySeparation
