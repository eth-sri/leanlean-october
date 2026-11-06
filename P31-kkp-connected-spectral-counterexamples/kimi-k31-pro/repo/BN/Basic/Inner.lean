module
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.Trace
@[expose] public section

namespace BN
open Matrix
open scoped Matrix
variable {n : Type*} [Fintype n]

/-- The real Frobenius pairing `⟨B, C⟩ = tr(Bᵀ C)`. -/
def inner (B C : Matrix n n ℝ) : ℝ := (Bᵀ * C).trace

lemma inner_add_left (B₁ B₂ C : Matrix n n ℝ) :
    inner (B₁ + B₂) C = inner B₁ C + inner B₂ C := by
  simp [inner, add_mul, trace_add]

lemma inner_add_right (B C₁ C₂ : Matrix n n ℝ) :
    inner B (C₁ + C₂) = inner B C₁ + inner B C₂ := by
  simp [inner, mul_add, trace_add]

lemma inner_smul_left (r : ℝ) (B C : Matrix n n ℝ) :
    inner (r • B) C = r * inner B C := by
  simp [inner, smul_mul, trace_smul, smul_eq_mul]

lemma inner_smul_right (r : ℝ) (B C : Matrix n n ℝ) :
    inner B (r • C) = r * inner B C := by
  simp [inner, Matrix.mul_smul, trace_smul, smul_eq_mul]

lemma inner_eq_sum (B C : Matrix n n ℝ) :
    inner B C = ∑ i, ∑ j, B i j * C i j := by
  simp only [inner, trace, diag, mul_apply, transpose_apply]
  rw [Finset.sum_comm]

lemma inner_self (B : Matrix n n ℝ) :
    inner B B = ∑ i, ∑ j, B i j ^ 2 := by
  simp [inner_eq_sum, pow_two]

/-- Spectral expansion in real rank-one terms. -/
lemma isHermitian_eq_sum_smul_vecMulVec [DecidableEq n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    A = ∑ k, hA.eigenvalues k •
      vecMulVec ((hA.eigenvectorUnitary : Matrix n n ℝ).col k)
        ((hA.eigenvectorUnitary : Matrix n n ℝ).col k) := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id, Function.id_comp]
  rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  ext a b
  rw [mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [mul_diagonal, transpose_apply, smul_eq_mul, vecMulVec_apply]
  ring

end BN
