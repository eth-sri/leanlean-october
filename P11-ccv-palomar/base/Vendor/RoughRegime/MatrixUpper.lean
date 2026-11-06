module

public import RoughRegime.Upper

@[expose] public section

/-!
Matrix spectral ingredients and the inverse-only (`N = 0`) specialization of Lemma 5(a).
The determinant-product case of that lemma is deliberately not claimed here.
-/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial RoughRegime.Upper
namespace RoughRegime.MatrixUpper

/-- The `k`th normalized Chebyshev polynomial on the positive interval. -/
def normalizedChebyshev (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ (k : ℤ)).comp
    (C (intervalHalfWidth lo hi)⁻¹ * (X - C (intervalCenter lo hi)))

lemma normalizedChebyshev_natDegree (lo hi : ℝ) (k : ℕ) :
    (normalizedChebyshev lo hi k).natDegree ≤ k := by
  unfold normalizedChebyshev
  calc
    _ ≤ (Polynomial.Chebyshev.T ℝ (k : ℤ)).natDegree *
      (C (intervalHalfWidth lo hi)⁻¹ * (X - C (intervalCenter lo hi))).natDegree :=
      natDegree_comp_le
    _ ≤ k * 1 := by
      apply Nat.mul_le_mul
      · simp [Polynomial.Chebyshev.natDegree_T]
      · exact (natDegree_C_mul_le _ _).trans (by simp)
    _ = k := by simp

lemma normalizedChebyshev_eval (lo hi x : ℝ) (k : ℕ) :
    (normalizedChebyshev lo hi k).eval x =
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) := by
  simp [normalizedChebyshev, div_eq_mul_inv, mul_comm]

/-- The Chebyshev coefficient has ℓ² operator norm at most one whenever the matrix spectrum
lies in the interval, exactly the spectral bound used before Lemma 5. -/
theorem matrix_chebyshev_norm_le_one {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M : Matrix n n ℝ) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) (k : ℕ) :
    ‖Polynomial.aeval M (normalizedChebyshev lo hi k)‖ ≤ 1 := by
  have hs : IsSelfAdjoint M := Matrix.isHermitian_iff_isSelfAdjoint.mp hM
  rw [← cfc_polynomial _ M hs]
  apply norm_cfc_le (by norm_num)
  intro x hx
  rw [normalizedChebyshev_eval, Real.norm_eq_abs]
  exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt (hSpec hx)) k

/-- Matrix whose entries are independent multivariate polynomial variables. -/
def variableMatrix (n : Type*) : Matrix n n (MvPolynomial (n × n) ℝ) :=
  fun i j => MvPolynomial.X (i, j)

lemma variableMatrix_power_degree {n : Type*} [Fintype n] [DecidableEq n]
    (k : ℕ) (i j : n) :
    ((variableMatrix n ^ k) i j).totalDegree ≤ k := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro a _
    exact (MvPolynomial.totalDegree_mul _ _).trans
      (Nat.add_le_add (ih i a) (by simp [variableMatrix]))

lemma variableMatrix_power_eval {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (k : ℕ) (i j : n) :
    MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2) ((variableMatrix n ^ k) i j) =
      (M ^ k) i j := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply, map_sum, map_mul, ih]
    simp [variableMatrix]

/-- Explicit entry polynomial for a univariate polynomial in a matrix. -/
def matrixEntryPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) : MvPolynomial (n × n) ℝ :=
  ∑ k ∈ Finset.range (q.natDegree + 1),
    MvPolynomial.C (q.coeff k) * (variableMatrix n ^ k) i j

lemma matrixEntryPolynomial_degree {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) :
    (matrixEntryPolynomial q i j).totalDegree ≤ q.natDegree := by
  unfold matrixEntryPolynomial
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  calc
    _ ≤ (MvPolynomial.C (q.coeff k) : MvPolynomial (n × n) ℝ).totalDegree +
      ((variableMatrix n ^ k) i j).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + k := Nat.add_le_add (by simp) (variableMatrix_power_degree k i j)
    _ ≤ q.natDegree := by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hk)

lemma matrixEntryPolynomial_eval {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (M : Matrix n n ℝ) (i j : n) :
    MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2) (matrixEntryPolynomial q i j) =
      (Polynomial.aeval M q) i j := by
  rw [Polynomial.aeval_eq_sum_range]
  unfold matrixEntryPolynomial
  simp only [map_sum, map_mul, MvPolynomial.eval_C, variableMatrix_power_eval,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]

end RoughRegime.MatrixUpper
