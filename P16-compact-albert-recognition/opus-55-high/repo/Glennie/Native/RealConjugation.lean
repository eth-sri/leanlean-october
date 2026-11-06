/- Real matrix conjugation for the explicit binary octonion matrix product.
Only real scalar associativity is used; no octonion matrix associativity is assumed.
-/
module

public import Glennie.Native.AlgebraLaws
public import Glennie.Obligations

@[expose] public section

open scoped BigOperators

namespace Glennie


def matrixRowMix (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) : Matrix (Fin 3) (Fin 3) Octonion :=
  fun i j => ∑ a, Q i a • A a j

def matrixColMix (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) : Matrix (Fin 3) (Fin 3) Octonion :=
  fun i j => ∑ a, Q j a • A i a

def matrixConjugateReal (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) : Matrix (Fin 3) (Fin 3) Octonion :=
  matrixRowMix Q (matrixColMix Q A)

def RealColumnsOrthogonal (Q : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  ∀ a b, ∑ k, Q k a * Q k b = if a = b then 1 else 0

theorem octMul_sum_left (f : Fin 3 → Octonion) (z : Octonion) :
    octMul (∑ i, f i) z = ∑ i, octMul (f i) z := by
  simp [Fin.sum_univ_three, octMul_add_left]

theorem octMul_sum_right (z : Octonion) (f : Fin 3 → Octonion) :
    octMul z (∑ i, f i) = ∑ i, octMul z (f i) := by
  simp [Fin.sum_univ_three, octMul_add_right]

theorem orth_sum (Q : Matrix (Fin 3) (Fin 3) ℝ) (hQ : RealColumnsOrthogonal Q)
    (f : Fin 3 → Fin 3 → Octonion) : ∑ k, ∑ a, ∑ b, (Q k a * Q k b) • f a b = ∑ a, f a a := by
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  simp [← Finset.sum_smul, hQ _ _]

theorem matrixMul_rowMix_left (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixMul (matrixRowMix Q A) B = matrixRowMix Q (matrixMul A B) := by
  ext i j : 1
  simp [matrixMul, matrixRowMix, octMul_sum_left, octMul_smul_left,
    Finset.smul_sum]
  rw [Finset.sum_comm]

theorem matrixMul_colMix_right (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixMul A (matrixColMix Q B) = matrixColMix Q (matrixMul A B) := by
  ext i j : 1
  simp [matrixMul, matrixColMix, octMul_sum_right, octMul_smul_right,
    Finset.smul_sum]
  rw [Finset.sum_comm]

theorem matrixMul_colMix_rowMix (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixMul (matrixColMix Q A) (matrixRowMix Q B) = matrixMul A B := by
  ext i j : 1
  simp [matrixMul, matrixColMix, matrixRowMix,
    octMul_sum_left, octMul_sum_right, octMul_smul_left, octMul_smul_right,
    Finset.smul_sum, smul_smul]
  exact orth_sum Q hQ fun b a => octMul (A i a) (B b j)

theorem matrixConjugateReal_mul (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixMul (matrixConjugateReal Q A) (matrixConjugateReal Q B) =
      matrixConjugateReal Q (matrixMul A B) := by
  rw [matrixConjugateReal, matrixConjugateReal, matrixMul_rowMix_left,
    matrixMul_colMix_rowMix Q hQ, matrixMul_colMix_right]
  rfl

theorem matrixConjugateReal_hermitian (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion)
    (hA : ∀ i j, octConj (A i j) = A j i) (i j : Fin 3) :
    octConj (matrixConjugateReal Q A i j) = matrixConjugateReal Q A j i := by
  simp [matrixConjugateReal, matrixRowMix, matrixColMix,
    octConj_sum, octConj_smul, hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm]

theorem matrixConjugateReal_add (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixConjugateReal Q (A+B) = matrixConjugateReal Q A + matrixConjugateReal Q B := by
  ext i j : 1
  simp [matrixConjugateReal, matrixRowMix, matrixColMix, smul_add, Finset.sum_add_distrib]

theorem matrixConjugateReal_smul (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (r : ℝ) (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixConjugateReal Q (r • A) = r • matrixConjugateReal Q A := by
  ext i j : 1
  simp [matrixConjugateReal, matrixRowMix, matrixColMix, Finset.smul_sum, smul_smul, mul_comm, mul_left_comm]

theorem matrixRowMix_comp (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixRowMix P (matrixRowMix Q A) = matrixRowMix (P*Q) A := by
  ext i j : 1
  simp [matrixRowMix, Matrix.mul_apply, Finset.smul_sum, smul_smul,
    Finset.sum_smul]
  rw [Finset.sum_comm]

theorem matrixColMix_comp (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixColMix P (matrixColMix Q A) = matrixColMix (P*Q) A := by
  ext i j : 1
  simp [matrixColMix, Matrix.mul_apply, Finset.smul_sum, smul_smul,
    Finset.sum_smul]
  rw [Finset.sum_comm]

theorem matrixColMix_rowMix (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixColMix P (matrixRowMix Q A) = matrixRowMix Q (matrixColMix P A) := by
  ext i j : 1
  simp [matrixColMix, matrixRowMix, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp [mul_comm]

theorem matrixConjugateReal_comp (P Q : Matrix (Fin 3) (Fin 3) ℝ)
    (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixConjugateReal P (matrixConjugateReal Q A) = matrixConjugateReal (P*Q) A := by
  simp [matrixConjugateReal, matrixColMix_rowMix, matrixRowMix_comp,
    matrixColMix_comp]

theorem matrixConjugateReal_one (A : Matrix (Fin 3) (Fin 3) Octonion) :
    matrixConjugateReal 1 A = A := by
  ext i j : 1
  simp [matrixConjugateReal, matrixRowMix, matrixColMix, Matrix.one_apply]

theorem real_transpose_mul_self (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) : Q.transpose * Q = 1 := by
  ext i j : 1
  simpa [Matrix.mul_apply, Matrix.one_apply, eq_comm] using hQ i j

theorem toMatrix_add (x y : Albert) : toMatrix (x+y) = toMatrix x+toMatrix y := by
  ext i j : 1
  change toMatrix (x+y) i j = toMatrix x i j + toMatrix y i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, octScalar, octConj_add]

theorem toMatrix_smul (r : ℝ) (x : Albert) : toMatrix (r • x) = r • toMatrix x := by
  ext i j : 1
  change toMatrix (r • x) i j = r • toMatrix x i j
  fin_cases i <;> fin_cases j <;>
    simp [toMatrix, octConj_smul, ← octScalar_smul]

theorem fromMatrix_add (A B : Matrix (Fin 3) (Fin 3) Octonion) :
    fromMatrix (A+B) = fromMatrix A+fromMatrix B := by rfl

theorem fromMatrix_smul (r : ℝ) (A : Matrix (Fin 3) (Fin 3) Octonion) :
    fromMatrix (r • A) = r • fromMatrix A := by rfl

def realConjugateAlbert (Q : Matrix (Fin 3) (Fin 3) ℝ) (x : Albert) : Albert :=
  fromMatrix (matrixConjugateReal Q (toMatrix x))

theorem toMatrix_realConjugateAlbert (Q : Matrix (Fin 3) (Fin 3) ℝ) (x : Albert) :
    toMatrix (realConjugateAlbert Q x) = matrixConjugateReal Q (toMatrix x) :=
  toMatrix_fromMatrix_hermitian _ (matrixConjugateReal_hermitian Q _ (toMatrix_hermitian x))

theorem realConjugateAlbert_jordan (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) (x y : Albert) :
    realConjugateAlbert Q (jordan x y) =
      jordan (realConjugateAlbert Q x) (realConjugateAlbert Q y) := by
  apply toMatrix_injective
  simp [toMatrix_realConjugateAlbert, toMatrix_jordan,
    matrixConjugateReal_smul, matrixConjugateReal_add,
    matrixConjugateReal_mul Q hQ]

def realConjugateAlbertEquiv (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) : Albert ≃ₗ[ℝ] Albert where
  toFun := realConjugateAlbert Q
  invFun := realConjugateAlbert Q.transpose
  left_inv x := by
    apply toMatrix_injective
    rw [toMatrix_realConjugateAlbert, toMatrix_realConjugateAlbert,
      matrixConjugateReal_comp, real_transpose_mul_self Q hQ, matrixConjugateReal_one]
  right_inv x := by
    apply toMatrix_injective
    rw [toMatrix_realConjugateAlbert, toMatrix_realConjugateAlbert, matrixConjugateReal_comp,
      mul_eq_one_comm.mp (real_transpose_mul_self Q hQ), matrixConjugateReal_one]
  map_add' x y := by
    simp [realConjugateAlbert, toMatrix_add, matrixConjugateReal_add, fromMatrix_add]
  map_smul' r x := by
    simp [realConjugateAlbert, toMatrix_smul, matrixConjugateReal_smul, fromMatrix_smul, RingHom.id_apply]

theorem matrixConjugateReal_diagonal_sum (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) (A : Matrix (Fin 3) (Fin 3) Octonion) :
    (∑ i, matrixConjugateReal Q A i i) = ∑ i, A i i := by
  simp [matrixConjugateReal, matrixRowMix, matrixColMix, Finset.smul_sum, smul_smul]
  exact orth_sum Q hQ A

theorem realConjugateAlbert_trace (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) (x : Albert) :
    trace (realConjugateAlbert Q x) = trace x := by
  have h := congrArg octRe (matrixConjugateReal_diagonal_sum Q hQ (toMatrix x))
  simpa [Fin.sum_univ_three, realConjugateAlbert, fromMatrix, trace, toMatrix, octRe, octScalar] using h

/-- Actual native automorphism, with both orthogonality identities checked by its caller. -/
def realOrthogonalAutomorphism (Q : Matrix (Fin 3) (Fin 3) ℝ)
    (hQ : RealColumnsOrthogonal Q) : CompactAutomorphism where
  equiv := realConjugateAlbertEquiv Q hQ
  map_jordan := realConjugateAlbert_jordan Q hQ
  map_trace := realConjugateAlbert_trace Q hQ

/-- Real rotation in the lower 2×2 block, in the exact upper-slot convention. -/
def realRotation12 (c s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![1,0,0],![0,c,s],![0,-s,c]]

theorem realRotation12_columns (c s : ℝ) (h : c^2+s^2=1) :
    RealColumnsOrthogonal (realRotation12 c s) := by
  intro a b
  fin_cases a <;> fin_cases b <;>
    simp [realRotation12, Fin.sum_univ_three] <;> nlinarith

def realRotation12Automorphism (c s : ℝ) (h : c^2+s^2=1) : CompactAutomorphism :=
  realOrthogonalAutomorphism (realRotation12 c s) (realRotation12_columns c s h)

attribute [local simp] realConjugateAlbert fromMatrix matrixConjugateReal matrixRowMix matrixColMix
  toMatrix Fin.sum_univ_three octRe

theorem realRotation12_d0 (c s : ℝ) (x : Albert) :
    (realConjugateAlbert (realRotation12 c s) x).d0 = x.d0 := by
  simp [realRotation12, octScalar]

theorem realRotation12_d1 (c s : ℝ) (x : Albert) :
    (realConjugateAlbert (realRotation12 c s) x).d1 =
      c^2*x.d1+s^2*x.d2+2*c*s*octRe x.o12 := by
  simp [realRotation12, oct_simps]
  ring

theorem realRotation12_d2 (c s : ℝ) (x : Albert) :
    (realConjugateAlbert (realRotation12 c s) x).d2 =
      s^2*x.d1+c^2*x.d2-2*c*s*octRe x.o12 := by
  simp [realRotation12, oct_simps]
  ring

def realSwap01 : Matrix (Fin 3) (Fin 3) ℝ := ![![0,1,0],![1,0,0],![0,0,1]]
def realSwap02 : Matrix (Fin 3) (Fin 3) ℝ := ![![0,0,1],![0,1,0],![1,0,0]]

def realSwap01Automorphism : CompactAutomorphism :=
  realOrthogonalAutomorphism realSwap01 (by
    intro a b; fin_cases a <;> fin_cases b <;> norm_num [realSwap01])

def realSwap02Automorphism : CompactAutomorphism :=
  realOrthogonalAutomorphism realSwap02 (by
    intro a b; fin_cases a <;> fin_cases b <;> norm_num [realSwap02])

theorem realSwap01_coordinates (x : Albert) :
    realConjugateAlbert realSwap01 x =
      ⟨x.d1,x.d0,x.d2,octConj x.o01,x.o12,x.o02⟩ := by
  apply Albert.ext <;> simp [realSwap01, octScalar]

theorem realSwap02_coordinates (x : Albert) :
    realConjugateAlbert realSwap02 x =
      ⟨x.d2,x.d1,x.d0,octConj x.o12,octConj x.o02,octConj x.o01⟩ := by
  apply Albert.ext <;> simp [realSwap02, octScalar]

end Glennie
