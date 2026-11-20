/- Real matrix conjugation for the explicit binary octonion matrix product.
Only real scalar associativity is used; no octonion matrix associativity is assumed.
-/
module

public import Glennie.Native.AlgebraLaws
public import Glennie.Obligations
public import Glennie.Sector
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.Module
@[expose] public section

open scoped BigOperators

namespace Glennie
noncomputable section

local notation "RealMat" => Matrix (Fin 3) (Fin 3) ℝ
local notation "OctMat" => Matrix (Fin 3) (Fin 3) Octonion

def matrixRowMix (Q : RealMat) : OctMat →ₗ[ℝ] OctMat where
  toFun A := Matrix.of fun i j => ∑ a, Q i a • A a j
  map_add' A B := Matrix.ext fun i j => by simp only [Matrix.of_apply, Matrix.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r A := Matrix.ext fun i j => by simp only [Matrix.of_apply, Matrix.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul, mul_comm]

def matrixColMix (Q : RealMat) : OctMat →ₗ[ℝ] OctMat :=
  let t := (Matrix.transposeLinearEquiv (Fin 3) (Fin 3) ℝ Octonion).toLinearMap
  (t.comp (matrixRowMix Q)).comp t

def matrixConjugateReal (Q : RealMat) := (matrixRowMix Q).comp (matrixColMix Q)

private theorem row_apply (Q : RealMat) (A : OctMat) (i j : Fin 3) :
    matrixRowMix Q A i j = ∑ a, Q i a • A a j := rfl
private theorem col_apply (Q : RealMat) (A : OctMat) (i j : Fin 3) :
    matrixColMix Q A i j = ∑ a, Q j a • A i a := rfl

abbrev RealColumnsOrthogonal (Q : RealMat) : Prop :=
  Q.transpose * Q = 1

theorem octMul_sum_left (f : Fin 3 → Octonion) (z : Octonion) :
    octMul (∑ i, f i) z = ∑ i, octMul (f i) z := by
  simp [Fin.sum_univ_three, octMul_add_left]

theorem octMul_sum_right (z : Octonion) (f : Fin 3 → Octonion) :
    octMul z (∑ i, f i) = ∑ i, octMul z (f i) := by
  simp [Fin.sum_univ_three, octMul_add_right]

theorem matrixMul_rowMix_left (Q : RealMat)
    (A B : OctMat) :
    matrixMul (matrixRowMix Q A) B = matrixRowMix Q (matrixMul A B) := by
  apply Matrix.ext
  intro i j
  simp only [matrixMul, row_apply, octMul_sum_left, octMul_smul_left,
    Finset.smul_sum]
  rw [Finset.sum_comm]

theorem matrixMul_colMix_right (Q : RealMat)
    (A B : OctMat) :
    matrixMul A (matrixColMix Q B) = matrixColMix Q (matrixMul A B) := by
  apply Matrix.ext
  intro i j
  simp only [matrixMul, col_apply, octMul_sum_right, octMul_smul_right,
    Finset.smul_sum]
  rw [Finset.sum_comm]

private theorem orthogonal_contract (Q : RealMat)
    (hQ : RealColumnsOrthogonal Q) (f : Fin 3 → Fin 3 → Octonion) :
    (∑ k, ∑ b, ∑ a, (Q k b * Q k a) • f a b) = ∑ a, f a a := by
  have he a b : ∑ k, Q k a * Q k b = (if a = b then 1 else 0) := by
    simpa [Matrix.mul_apply, Matrix.one_apply, eq_comm] using congrArg (fun A : RealMat => A a b) hQ
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  simp [← Finset.sum_smul, he, ite_smul]

theorem matrixMul_colMix_rowMix (Q : RealMat)
    (hQ : RealColumnsOrthogonal Q) (A B : OctMat) :
    matrixMul (matrixColMix Q A) (matrixRowMix Q B) = matrixMul A B := by
  apply Matrix.ext
  intro i j
  simpa only [matrixMul, col_apply, row_apply, octMul_sum_left, octMul_sum_right,
    octMul_smul_left, octMul_smul_right, Finset.smul_sum, smul_smul] using
    orthogonal_contract Q hQ (fun a b => octMul (A i a) (B b j))

theorem matrixConjugateReal_mul (Q : RealMat)
    (hQ : RealColumnsOrthogonal Q)
    (A B : OctMat) :
    matrixMul (matrixConjugateReal Q A) (matrixConjugateReal Q B) =
      matrixConjugateReal Q (matrixMul A B) := by
  simp only [matrixConjugateReal, LinearMap.comp_apply, matrixMul_rowMix_left, matrixMul_colMix_rowMix Q hQ, matrixMul_colMix_right]

theorem matrixConjugateReal_hermitian (Q : RealMat)
    (A : OctMat)
    (hA : ∀ i j, octConj (A i j) = A j i) (i j : Fin 3) :
    octConj (matrixConjugateReal Q A i j) = matrixConjugateReal Q A j i := by
  simp only [matrixConjugateReal, LinearMap.comp_apply, row_apply, col_apply,
    octConj_sum, octConj_smul, hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

open scoped Matrix.Module in
theorem matrixRowMix_comp (P Q : RealMat) (A : OctMat) :
    matrixRowMix P (matrixRowMix Q A) = matrixRowMix (P*Q) A :=
  Matrix.ext fun i j => congrFun (mul_smul P Q (fun k => A k j)).symm i

theorem matrixColMix_comp (P Q : RealMat)
    (A : OctMat) :
    matrixColMix P (matrixColMix Q A) = matrixColMix (P*Q) A := by
  exact congrArg Matrix.transpose (matrixRowMix_comp P Q A.transpose)

theorem matrixColMix_rowMix (P Q : RealMat)
    (A : OctMat) :
    matrixColMix P (matrixRowMix Q A) = matrixRowMix Q (matrixColMix P A) := by
  apply Matrix.ext
  intro i j
  simp only [col_apply, row_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem matrixConjugateReal_comp (P Q : RealMat)
    (A : OctMat) :
    matrixConjugateReal P (matrixConjugateReal Q A) = matrixConjugateReal (P*Q) A := by
  simp only [matrixConjugateReal, LinearMap.comp_apply, matrixColMix_rowMix, matrixRowMix_comp,
    matrixColMix_comp]

theorem matrixConjugateReal_one (A : OctMat) :
    matrixConjugateReal 1 A = A := by
  apply Matrix.ext
  intro i j
  simp [matrixConjugateReal, LinearMap.comp_apply, row_apply, col_apply, Matrix.one_apply]

theorem toMatrix_add (x y : Albert) : toMatrix (x+y) = toMatrix x+toMatrix y := by
  apply Matrix.ext
  intro i j
  change toMatrix (x+y) i j = toMatrix x i j + toMatrix y i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, octScalar, octConj_add]

theorem toMatrix_smul (r : ℝ) (x : Albert) : toMatrix (r • x) = r • toMatrix x := by
  apply Matrix.ext
  intro i j
  change toMatrix (r • x) i j = r • toMatrix x i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, octConj_smul, ← octScalar_smul]

def realConjugateAlbert (Q : RealMat) (x : Albert) : Albert :=
  fromMatrix (matrixConjugateReal Q (toMatrix x))

theorem toMatrix_realConjugateAlbert (Q : RealMat) (x : Albert) :
    toMatrix (realConjugateAlbert Q x) = matrixConjugateReal Q (toMatrix x) :=
  toMatrix_fromMatrix_hermitian _ (matrixConjugateReal_hermitian Q _ (toMatrix_hermitian x))

theorem realConjugateAlbert_jordan (Q : RealMat)
    (hQ : RealColumnsOrthogonal Q) (x y : Albert) :
    realConjugateAlbert Q (jordan x y) =
      jordan (realConjugateAlbert Q x) (realConjugateAlbert Q y) := by
  apply toMatrix_injective
  simp only [toMatrix_realConjugateAlbert, toMatrix_jordan,
    map_smul, map_add,
    matrixConjugateReal_mul Q hQ]

def realConjugateAlbertEquiv (Q : RealMat)
    (hQ : RealColumnsOrthogonal Q) :
    Albert ≃ₗ[ℝ] Albert where
  toFun := realConjugateAlbert Q
  invFun := realConjugateAlbert Q.transpose
  left_inv x := toMatrix_injective (by
    simp only [toMatrix_realConjugateAlbert, matrixConjugateReal_comp, hQ, matrixConjugateReal_one])
  right_inv x := toMatrix_injective (by
    simp only [toMatrix_realConjugateAlbert, matrixConjugateReal_comp, mul_eq_one_comm.mp hQ,
      matrixConjugateReal_one])
  map_add' x y := toMatrix_injective (by simp only [toMatrix_realConjugateAlbert, toMatrix_add, map_add])
  map_smul' r x := toMatrix_injective (by simp only [toMatrix_realConjugateAlbert, toMatrix_smul, map_smul, RingHom.id_apply])

theorem matrixConjugateReal_diagonal_sum (Q : RealMat)
    (hQ : RealColumnsOrthogonal Q) (A : OctMat) :
    (∑ i, matrixConjugateReal Q A i i) = ∑ i, A i i := by
  simpa only [matrixConjugateReal, LinearMap.comp_apply, row_apply, col_apply, Finset.smul_sum, smul_smul] using
    orthogonal_contract Q hQ (fun a b => A b a)

theorem realConjugateAlbert_trace (Q : RealMat)
    (hQ : RealColumnsOrthogonal Q) (x : Albert) :
    trace (realConjugateAlbert Q x) = trace x := by
  have h := congrArg octRe (matrixConjugateReal_diagonal_sum Q hQ (toMatrix x))
  simpa [Fin.sum_univ_three, realConjugateAlbert, fromMatrix, trace, toMatrix, octRe, octScalar] using h

/-- Actual native automorphism, with both orthogonality identities checked by its caller. -/
def realOrthogonalAutomorphism (Q : RealMat)
    (hQ : RealColumnsOrthogonal Q) :
    CompactAutomorphism where
  equiv := realConjugateAlbertEquiv Q hQ
  map_jordan := realConjugateAlbert_jordan Q hQ
  map_trace := realConjugateAlbert_trace Q hQ

/-- Real rotation in the lower 2×2 block, in the exact upper-slot convention. -/
def realRotation12 (c s : ℝ) : RealMat :=
  ![![1,0,0],![0,c,s],![0,-s,c]]

theorem realRotation12_columns (c s : ℝ) (h : c^2+s^2=1) :
    RealColumnsOrthogonal (realRotation12 c s) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply]
  change (∑ k, realRotation12 c s k i * realRotation12 c s k j) = _
  fin_cases i <;> fin_cases j <;>
    simp [realRotation12, Fin.sum_univ_three] <;> nlinarith

def realRotation12Automorphism (c s : ℝ) (h : c^2+s^2=1) : CompactAutomorphism :=
  realOrthogonalAutomorphism (realRotation12 c s) (realRotation12_columns c s h)

theorem realRotation12_diag (c s : ℝ) (x : Albert) (i : Fin 3) :
    octRe (toMatrix (realConjugateAlbert (realRotation12 c s) x) i i) =
      ![x.d0, c^2*x.d1+s^2*x.d2+2*c*s*octRe x.o12,
        s^2*x.d1+c^2*x.d2-2*c*s*octRe x.o12] i := by
  simp only [toMatrix_realConjugateAlbert, matrixConjugateReal, LinearMap.comp_apply, row_apply, col_apply]
  fin_cases i <;> simp [realRotation12, toMatrix, Fin.sum_univ_three, octRe, octScalar, octConj, smul_eq_mul] <;> ring

def permutationAutomorphism (s : Equiv.Perm (Fin 3)) : CompactAutomorphism :=
  realOrthogonalAutomorphism (s.permMatrix ℝ) <| by
    unfold RealColumnsOrthogonal
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

@[simp] theorem toMatrix_permutation (s : Equiv.Perm (Fin 3)) (x : Albert) (i j : Fin 3) :
    toMatrix ((permutationAutomorphism s).equiv x) i j = toMatrix x (s i) (s j) := by
  change toMatrix (realConjugateAlbert (s.permMatrix ℝ) x) i j = _
  rw [toMatrix_realConjugateAlbert]
  simp [matrixConjugateReal, LinearMap.comp_apply, row_apply, col_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, ite_smul]

abbrev diagonalOf (v : Fin 3 → ℝ) : Albert := diagonalAlbert (v 0) (v 1) (v 2)

theorem toMatrix_diagonalOf (v : Fin 3 → ℝ) (i j : Fin 3) :
    toMatrix (diagonalOf v) i j = (Matrix.diagonal fun k => octScalar (v k)) i j := by
  fin_cases i <;> fin_cases j <;> simp [diagonalOf, toMatrix, diagonalAlbert, octConj]

theorem permutation_diagonalOf (s : Equiv.Perm (Fin 3)) (v : Fin 3 → ℝ) :
    (permutationAutomorphism s).equiv (diagonalOf v) = diagonalOf (v ∘ s) := by
  apply toMatrix_injective
  apply Matrix.ext
  intro i j
  simp [toMatrix_diagonalOf, Matrix.diagonal_apply, s.injective.eq_iff]

end
end Glennie
