module

public import RoughRegime.MatrixUpper
public import RoughRegime.SeriesBounds

@[expose] public section

/-!
# Determinant coefficients of the matrix reciprocal kernel

The formal determinant series is built from entry polynomials in the actual
matrix variables. Its kth coefficient has total degree at most k.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial

namespace RoughRegime.MatrixDeterminant

open RoughRegime.Upper RoughRegime.MatrixUpper

section
variable {V I n : Type*}

/-- Degree-compatible products of polynomial-valued power series. -/
theorem coeff_totalDegree_mul_le
    (f g : PowerSeries (MvPolynomial V ℝ))
    (hf : ∀ k, (PowerSeries.coeff k f).totalDegree ≤ k)
    (hg : ∀ k, (PowerSeries.coeff k g).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k (f * g)).totalDegree ≤ k := by
  rw [PowerSeries.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ij hij
  exact (MvPolynomial.totalDegree_mul _ _).trans
    ((Nat.add_le_add (hf ij.1) (hg ij.2)).trans_eq
      (Finset.HasAntidiagonal.mem_antidiagonal.mp hij))

/-- Finite products preserve total degree bounded by the series index. -/
theorem coeff_totalDegree_prod_le [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries (MvPolynomial V ℝ))
    (hf : ∀ i ∈ s, ∀ k, (PowerSeries.coeff k (f i)).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k (∏ i ∈ s, f i)).totalDegree ≤ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp
    split_ifs <;> simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    apply coeff_totalDegree_mul_le <;> aesop

/-- Taking a determinant does not increase the total degree of its kth coefficient. -/
theorem determinant_coefficient_totalDegree_le [Fintype n] [DecidableEq n]
    (M : Matrix n n (PowerSeries (MvPolynomial V ℝ)))
    (hM : ∀ i j k, (PowerSeries.coeff k (M i j)).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k M.det).totalDegree ≤ k := by
  rw [Matrix.det_apply, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  exact (MvPolynomial.totalDegree_smul_le _ _).trans
    (coeff_totalDegree_prod_le Finset.univ (fun i => M (σ i) i) (by
      tauto) k)

end

/-- Scalar Chebyshev polynomial giving the kth normalized reciprocal-kernel coefficient. -/
def kernelCoefficientPolynomial (lo hi : ℝ) (k : ℕ) : ℝ[X] :=
  C (if k = 0 then 1 else 2 * (-intervalRho lo hi) ^ k) * normalizedChebyshev lo hi k

lemma kernelCoefficientPolynomial_natDegree (lo hi : ℝ) (k : ℕ) :
    (kernelCoefficientPolynomial lo hi k).natDegree ≤ k :=
  (natDegree_C_mul_le _ _).trans (normalizedChebyshev_natDegree ..)

section
variable (lo hi : ℝ) {n : Type*} [Fintype n] [DecidableEq n]

/-- Reciprocal-kernel entry series in independent matrix-entry variables. -/
def variableKernelSeries :
    Matrix n n (PowerSeries (MvPolynomial (n × n) ℝ)) := fun i j =>
  PowerSeries.mk (fun k => matrixEntryPolynomial (kernelCoefficientPolynomial lo hi k) i j)

/-- The determinant coefficient is an actual polynomial in all the matrix entries. -/
def determinantCoefficientPolynomial
    (k : ℕ) : MvPolynomial (n × n) ℝ :=
  PowerSeries.coeff k (variableKernelSeries lo hi).det

theorem determinantCoefficientPolynomial_totalDegree
    (lo hi : ℝ) (k : ℕ) :
    (determinantCoefficientPolynomial lo hi (n := n) k).totalDegree ≤ k := by
  apply determinant_coefficient_totalDegree_le
  intro i j t
  simp [variableKernelSeries]
  exact (matrixEntryPolynomial_degree _ i j).trans (kernelCoefficientPolynomial_natDegree ..)

/-- The actual matrix kernel as a matrix of formal real power series. -/
def kernelSeries
    (M : Matrix n n ℝ) : Matrix n n (PowerSeries ℝ) := fun i j =>
  PowerSeries.mk (fun k => (Polynomial.aeval M (kernelCoefficientPolynomial lo hi k)) i j)

/-- Evaluation of all matrix variables produces the actual kernel entry series. -/
theorem variableKernelSeries_map_eval
    (lo hi : ℝ) (M : Matrix n n ℝ) :
    (PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij => M ij.1 ij.2))).mapMatrix
      (variableKernelSeries lo hi) = kernelSeries lo hi M := by
  ext i j k
  exact matrixEntryPolynomial_eval _ M i j

/-- Each polynomial coefficient evaluates to the kth coefficient of the actual kernel determinant. -/
theorem determinantCoefficientPolynomial_eval
    (lo hi : ℝ) (M : Matrix n n ℝ) (k : ℕ) :
    MvPolynomial.eval (fun ij => M ij.1 ij.2)
      (determinantCoefficientPolynomial lo hi k) =
      PowerSeries.coeff k (kernelSeries lo hi M).det := by
  let φ := MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij : n × n => M ij.1 ij.2)
  have he := congrArg (fun f => PowerSeries.coeff k f)
    ((PowerSeries.map φ).map_det (variableKernelSeries lo hi))
  rw [variableKernelSeries_map_eval] at he
  assumption

end

/-- Scalar series corresponding to one eigenvalue of the reciprocal kernel. -/
def scalarKernelSeries (lo hi x : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => (kernelCoefficientPolynomial lo hi k).eval x)

private theorem aeval_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (d : n → ℝ) :
    Polynomial.aeval (Matrix.diagonal d) q = Matrix.diagonal (fun i => q.eval (d i)) := by
  change Polynomial.aeval ((Matrix.diagonalAlgHom ℝ) d) q = _
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_pi_apply]
  rfl

def coefficientMatrix {n : Type*} (k : ℕ) (M : Matrix n n (PowerSeries ℝ)) :
    Matrix n n ℝ := fun i j => PowerSeries.coeff k (M i j)

section
variable {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (M : Matrix n n (PowerSeries ℝ))
    (k : ℕ)

theorem coefficientMatrix_constant_mul :
    coefficientMatrix k ((PowerSeries.C.mapMatrix A) * M) = A * coefficientMatrix k M := by
  ext i j
  simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_C_mul]

theorem coefficientMatrix_mul_constant :
    coefficientMatrix k (M * (PowerSeries.C.mapMatrix A)) = coefficientMatrix k M * A := by
  ext i j
  simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_mul_C]

end

theorem coefficientMatrix_diagonal {n : Type*} [DecidableEq n]
    (d : n → PowerSeries ℝ) (k : ℕ) :
    coefficientMatrix k (Matrix.diagonal d) = Matrix.diagonal (fun i => PowerSeries.coeff k (d i)) := by
  ext i j
  simp only [coefficientMatrix, Matrix.diagonal_apply]
  split_ifs <;> simp

section
variable {n : Type*} [Fintype n] [DecidableEq n] (lo hi : ℝ) {M : Matrix n n ℝ} (hM : M.IsHermitian)

/-- The actual formal matrix kernel diagonalizes in the same fixed eigenbasis as its argument. -/
theorem kernelSeries_spectral :
    kernelSeries lo hi M =
      (PowerSeries.C.mapMatrix hM.eigenvectorUnitary) *
      Matrix.diagonal (fun i => scalarKernelSeries lo hi (hM.eigenvalues i)) *
      (PowerSeries.C.mapMatrix (star hM.eigenvectorUnitary)) := by
  ext i j k
  change _ =
    (coefficientMatrix k (_ * _ * _)) i j
  rw [coefficientMatrix_mul_constant, coefficientMatrix_constant_mul, coefficientMatrix_diagonal]
  simp [coefficientMatrix, kernelSeries, scalarKernelSeries]
  have hp := Polynomial.aeval_algHom_apply
    (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hM.eigenvectorUnitary)
    (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues))
    (kernelCoefficientPolynomial lo hi k)
  rw [← hM.spectral_theorem, aeval_diagonal] at hp
  solve_by_elim [congrArg]

/-- The formal determinant is exactly the product of the scalar eigenvalue reciprocal series. -/
theorem kernelSeries_det_spectral :
    (kernelSeries lo hi M).det = ∏ i, scalarKernelSeries lo hi (hM.eigenvalues i) := by
  rw [kernelSeries_spectral lo hi hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hu :
      (PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)).det *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))).det = 1 := by
    rw [← Matrix.det_mul, ← map_mul]
    simp
  grind

end

section
variable {lo hi x : ℝ} (hlo : 0 < lo) (hlt : lo < hi) (hx : x ∈ Set.Icc lo hi)
include hlo hlt hx

/-- Scalar kernel coefficients have the same geometric bound as in the paper. -/
theorem scalarKernelSeries_coefficient_norm_le (k : ℕ) :
    ‖PowerSeries.coeff k (scalarKernelSeries lo hi x)‖ ≤ 2 * intervalRho lo hi ^ k := by
  have hr := intervalRho_pos lo hi hlo hlt
  have ht : |(normalizedChebyshev lo hi k).eval x| ≤ 1 := by
    rw [normalizedChebyshev_eval]
    solve_by_elim [chebyshev_abs_le_one, interval_argument_mem]
  simp [scalarKernelSeries, kernelCoefficientPolynomial]
  by_cases hk : k = 0
  · subst k
    simp [normalizedChebyshev]
  · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow, abs_neg,
      abs_of_pos hr]
    bound

/-- Absolute summability of every scalar eigenvalue kernel. -/
theorem scalarKernelSeries_summable_norm :
    Summable (fun k => ‖PowerSeries.coeff k (scalarKernelSeries lo hi x)‖) := by
  have hg := (summable_geometric_of_lt_one (intervalRho_pos lo hi hlo hlt).le
    (intervalRho_lt_one lo hi hlo hlt)).mul_left 2
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (scalarKernelSeries_coefficient_norm_le hlo hlt hx) hg

/-- At z=1 the scalar formal kernel sums to the normalized reciprocal. -/
theorem scalarKernelSeries_tsum :
    (∑' k, PowerSeries.coeff k (scalarKernelSeries lo hi x)) = intervalGeometricMean lo hi / x := by
  rw [((scalarKernelSeries_summable_norm hlo hlt hx).of_norm).tsum_eq_zero_add]
  simp only [scalarKernelSeries, PowerSeries.coeff_mk, kernelCoefficientPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.add_one_ne_zero, ite_false,
    normalizedChebyshev_eval]
  norm_num only [ Polynomial.Chebyshev.T_zero, Polynomial.eval_one,
    ite_true]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  exact reciprocal_real_series lo hi x hlo hlt hx

end

section
variable {R I : Type*} [NormedCommRing R]

/-- Absolute convergence is stable under the genuine finite Cauchy product. -/
theorem powerSeries_prod_summable_norm [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries R)
    (hf : ∀ i ∈ s, Summable (fun k => ‖PowerSeries.coeff k (f i)‖)) :
    Summable (fun k => ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖) := by
  induction s using Finset.induction_on with
  | empty =>
    apply summable_of_ne_finset_zero (s := {0})
    aesop
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm
      (hf a (Finset.mem_insert_self ..))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
    convert hs using 1
    funext k
    rw [PowerSeries.coeff_mul]

/-- The sum of the coefficients of a finite product is the product of their sums. -/
theorem powerSeries_prod_tsum [CompleteSpace R] [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries R)
    (hf : ∀ i ∈ s, Summable (fun k => ‖PowerSeries.coeff k (f i)‖)) :
    (∑' k, PowerSeries.coeff k (∏ i ∈ s, f i)) = ∏ i ∈ s, ∑' k, PowerSeries.coeff k (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hc : (fun k => PowerSeries.coeff k (f a * ∏ i ∈ s, f i)) =
        RoughRegime.SeriesBounds.convolution
          (fun k => PowerSeries.coeff k (f a))
          (fun k => PowerSeries.coeff k (∏ i ∈ s, f i)) := by
      funext k
      exact PowerSeries.coeff_mul k _ _
    rw [hc, RoughRegime.SeriesBounds.convolution_tsum]
    · rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]
    · exact hf a (Finset.mem_insert_self ..)
    · exact powerSeries_prod_summable_norm s f
        (fun i hi => hf i (Finset.mem_insert_of_mem hi))

end

variable {n : Type*} [Fintype n] [DecidableEq n] {lo hi : ℝ} (hlo : 0 < lo) (hlt : lo < hi)
    {M : Matrix n n ℝ} (hM : M.IsHermitian) (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi)
include hM hSpec hlo hlt

/-- Absolute convergence of the actual formal determinant coefficients. -/
theorem kernelSeries_det_summable_norm :
    Summable (fun k => ‖PowerSeries.coeff k (kernelSeries lo hi M).det‖) := by
  rw [kernelSeries_det_spectral lo hi hM]
  apply powerSeries_prod_summable_norm
  intro i _
  exact scalarKernelSeries_summable_norm hlo hlt
    (hSpec (hM.eigenvalues_mem_spectrum_real i))

/-- The actual determinant series sums to the normalized determinant reciprocal. -/
theorem kernelSeries_det_tsum :
    (∑' k, PowerSeries.coeff k (kernelSeries lo hi M).det) =
      intervalGeometricMean lo hi ^ Fintype.card n / M.det := by
  rw [kernelSeries_det_spectral lo hi hM, powerSeries_prod_tsum]
  · simp_rw [scalarKernelSeries_tsum hlo hlt
      (hSpec (hM.eigenvalues_mem_spectrum_real _))]
    rw [Finset.prod_div_distrib]
    simp
    rw [hM.det_eq_prod_eigenvalues]
    rfl
  · intro i _
    exact scalarKernelSeries_summable_norm hlo hlt
      (hSpec (hM.eigenvalues_mem_spectrum_real i))

end RoughRegime.MatrixDeterminant
