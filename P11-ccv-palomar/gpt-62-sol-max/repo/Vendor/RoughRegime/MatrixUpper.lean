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
      · simp
      · exact (natDegree_C_mul_le _ _).trans (by simp)
    _ = k := by simp

lemma normalizedChebyshev_eval (lo hi x : ℝ) (k : ℕ) :
    (normalizedChebyshev lo hi k).eval x =
      (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) := by
  simp [normalizedChebyshev, div_eq_mul_inv, mul_comm]

/-- The Chebyshev coefficient has ℓ² operator norm at most one whenever the matrix spectrum
lies in the interval, exactly the spectral bound used before Lemma 5. -/
theorem normalizedChebyshev_aeval_norm_le_one {A : Type*} [NormedRing A] [StarRing A]
    [NormedAlgebra ℝ A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : A) (hM : IsSelfAdjoint M)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) (k : ℕ) :
    ‖Polynomial.aeval M (normalizedChebyshev lo hi k)‖ ≤ 1 := by
  rw [← cfc_polynomial _ M hM]
  apply norm_cfc_le (by norm_num)
  intro x hx
  rw [normalizedChebyshev_eval, Real.norm_eq_abs]
  exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt (hSpec hx)) k

/-- Matrix whose entries are independent multivariate polynomial variables. -/
def variableMatrix (n : Type*) : Matrix n n (MvPolynomial (n × n) ℝ) :=
  fun i j => MvPolynomial.X (i, j)

section
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma variableMatrix_power_degree
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

end

/-- Explicit entry polynomial for a univariate polynomial in a matrix. -/
def matrixEntryPolynomial {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) : MvPolynomial (n × n) ℝ :=
  (aeval (variableMatrix n) q) i j

section
variable {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X])

lemma matrixEntryPolynomial_degree (i j : n) :
    (matrixEntryPolynomial q i j).totalDegree ≤ q.natDegree := by
  simp only [matrixEntryPolynomial, aeval_eq_sum_range, Matrix.sum_apply, Matrix.smul_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  rw [Algebra.smul_def, MvPolynomial.algebraMap_eq]
  calc
    _ ≤ (MvPolynomial.C (q.coeff k) : MvPolynomial (n × n) ℝ).totalDegree +
      ((variableMatrix n ^ k) i j).totalDegree := MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + k := Nat.add_le_add (by simp) (variableMatrix_power_degree k i j)
    _ ≤ q.natDegree := by simp_all

lemma matrixEntryPolynomial_eval {K : Type*} [CommRing K] [Algebra ℝ K] (M : Matrix n n K) (i j : n) :
    MvPolynomial.eval₂ (algebraMap ℝ K) (fun ij : n × n => M ij.1 ij.2) (matrixEntryPolynomial q i j) =
      (Polynomial.aeval M q) i j := by
  let φ : Matrix n n (MvPolynomial (n × n) ℝ) →ₐ[ℝ] Matrix n n K :=
    (MvPolynomial.aeval (fun ij : n × n => M ij.1 ij.2)).mapMatrix
  have hφ : φ (variableMatrix n) = M := by ext i j; simp [φ, variableMatrix]
  have h := Polynomial.aeval_algHom_apply φ (variableMatrix n) q
  rw [hφ] at h
  exact (congrArg (fun A : Matrix n n K => A i j) h).symm

end

end RoughRegime.MatrixUpper
