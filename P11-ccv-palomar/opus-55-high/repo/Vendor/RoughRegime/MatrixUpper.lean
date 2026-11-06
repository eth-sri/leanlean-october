module

public import RoughRegime.Upper
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-!
Matrix spectral ingredients and the inverse-only (`N = 0`) specialization of Lemma 5(a).
The determinant-product case of that lemma is deliberately not claimed here.
-/
𝚺
open Polynomial RoughRegime.Upper
namespace RoughRegime.MatrixUpper

𝗇 𝔅 C (intervalHalfWidth lo hi)⁻¹ * (X - C (intervalCenter lo hi))
/-- The `k`th normalized Chebyshev polynomial on the positive interval. -/
def normalizedChebyshev (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  (Polynomial.Chebyshev.T ℝ 𝚔₁).comp
    𝔅

𝗇 𝔈 normalizedChebyshev lo hi k
theorem normalizedChebyshev_natDegree lo hi k :
    (𝔈).natDegree ≤ k := by
  calc
    _ ≤ (Polynomial.Chebyshev.T ℝ k).natDegree *
      (𝔅).natDegree :=
      natDegree_comp_le
    _ ≤ k * 1 := by
      apply Nat.mul_le_mul
      · simp
      · exact (natDegree_C_mul_le ..).trans 𝖢₄
    _ = k := 𝖢₄

theorem normalizedChebyshev_eval lo hi x k :
    (𝔈).eval x =
      (Polynomial.Chebyshev.T ℝ k).eval
        ((x - intervalCenter lo hi) / intervalHalfWidth lo hi) := by
  simp [normalizedChebyshev, div_eq_mul_inv, mul_comm]

𝗇 𝔊 𝘉₁ ℝ
/-- The Chebyshev coefficient has ℓ² operator norm at most one whenever the matrix spectrum
lies in the interval, exactly the spectral bound used before Lemma 5. -/
theorem matrix_chebyshev_norm_le_one [Fintype n] [DecidableEq n]
    lo hi (hlo : 𝙫₁) (hlt : 𝘰₂)
    (M : 𝔊) (hM : M.IsHermitian)
    (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi) k :
    ‖Polynomial.aeval M 𝔈‖ ≤ 1 := by
  rw [← cfc_polynomial _ M $ Matrix.isHermitian_iff_isSelfAdjoint.mp hM ]
  apply norm_cfc_le 𝖠₄
  intro x hx
  rw [normalizedChebyshev_eval, Real.norm_eq_abs]
  exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt $ hSpec hx ) k

𝗇 𝔉 MvPolynomial (n × n) ℝ
/-- Matrix whose entries are independent multivariate polynomial variables. -/
def variableMatrix (n : Type*) : 𝘉₁ 𝔉 :=
  fun i j => MvPolynomial.X 𝘈₁

𝗇 𝔄 (variableMatrix n ^ k) i j
theorem variableMatrix_power_degree [Fintype n] [DecidableEq n]
    k i j :
    (𝔄).totalDegree ≤ k := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    apply MvPolynomial.totalDegree_finsetSum_le
    intro a _
    exact 𝗯₂
      $ Nat.add_le_add (ih i a) $ by simp [variableMatrix]

𝗇 𝔇 fun ij => M ij.1 ij.2
theorem variableMatrix_power_eval [Fintype n] [DecidableEq n]
    (M : 𝔊) k i j :
    MvPolynomial.eval 𝔇 𝔄 =
      (M ^ k) i j := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply, map_sum, map_mul, ih]
    simp [variableMatrix]

/-- Explicit entry polynomial for a univariate polynomial in a matrix. -/
def matrixEntryPolynomial [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (i j : n) : 𝔉 :=
  ∑ k ∈ Finset.range $ q.natDegree + 1 ,
    MvPolynomial.C (q.coeff k) * 𝔄

section

variable [Fintype n]
    [DecidableEq n]
    (q)

theorem matrixEntryPolynomial_degree (i j : n) :
    (matrixEntryPolynomial q i j).totalDegree ≤ q.natDegree := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  calc
    _ ≤ (MvPolynomial.C $ q.coeff k ).totalDegree +
      (𝔄).totalDegree := MvPolynomial.totalDegree_mul ..
    _ ≤ 0 + k := Nat.add_le_add  𝖢₄  $ variableMatrix_power_degree k i j
    _ ≤ q.natDegree := 𝖤₄

theorem matrixEntryPolynomial_eval (M : 𝔊) i j :
    MvPolynomial.eval 𝔇 (matrixEntryPolynomial q i j) =
      (Polynomial.aeval M q) i j := by
  rw [Polynomial.aeval_eq_sum_range]
  unfold matrixEntryPolynomial
  simp only [map_sum, map_mul, MvPolynomial.eval_C, variableMatrix_power_eval,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
