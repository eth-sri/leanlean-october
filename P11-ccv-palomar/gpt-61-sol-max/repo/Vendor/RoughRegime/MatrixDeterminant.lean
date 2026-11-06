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

/-- Degree-compatible products of polynomial-valued power series. -/
theorem coeff_totalDegree_mul_le {V : Type*}
    (f g : PowerSeries (MvPolynomial V ℝ))
    (hf : ∀ k, (PowerSeries.coeff k f).totalDegree ≤ k)
    (hg : ∀ k, (PowerSeries.coeff k g).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k (f * g)).totalDegree ≤ k := by
  rw [PowerSeries.coeff_mul]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro ij hij
  grind only [MvPolynomial.totalDegree_mul, Finset.HasAntidiagonal.mem_antidiagonal.mp]

/-- Finite products preserve total degree bounded by the series index. -/
theorem coeff_totalDegree_prod_le {V I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries (MvPolynomial V ℝ))
    (hf : ∀ i ∈ s, ∀ k, (PowerSeries.coeff k (f i)).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k (∏ i ∈ s, f i)).totalDegree ≤ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs <;> simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    simp_all [coeff_totalDegree_mul_le]

/-- Taking a determinant does not increase the total degree of its kth coefficient. -/
theorem determinant_coefficient_totalDegree_le {V n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n (PowerSeries (MvPolynomial V ℝ)))
    (hM : ∀ i j k, (PowerSeries.coeff k (M i j)).totalDegree ≤ k) (k : ℕ) :
    (PowerSeries.coeff k M.det).totalDegree ≤ k := by
  rw [Matrix.det_apply, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro σ _
  simp only [Units.smul_def]
  exact (MvPolynomial.totalDegree_smul_le _ _).trans
    (coeff_totalDegree_prod_le Finset.univ (fun i => M (σ i) i) (by
      intro i _
      exact hM (σ i) i) k)

/-- Scalar Chebyshev polynomial giving the kth normalized reciprocal-kernel coefficient. -/
def kernelCoefficientPolynomial lo hi k  :=
  C (if k = 0 then 1 else 2 * (-intervalRho lo hi) ^ k) * normalizedChebyshev lo hi k

lemma kernelCoefficientPolynomial_natDegree (lo hi : ℝ) (k : ℕ) :
    (kernelCoefficientPolynomial lo hi k).natDegree ≤ k :=
  (natDegree_C_mul_le _ _).trans (normalizedChebyshev_natDegree lo hi k)

section
variable (lo hi : ℝ) {n : Type*}
include lo hi

/-- Reciprocal-kernel entry series in independent matrix-entry variables. -/
def variableKernelSeries  [Fintype n] [DecidableEq n] :
    Matrix n n (PowerSeries (MvPolynomial (n × n) ℝ)) := fun i j =>
  PowerSeries.mk (fun k => matrixEntryPolynomial (kernelCoefficientPolynomial lo hi k) i j)

/-- The determinant coefficient is an actual polynomial in all the matrix entries. -/
def determinantCoefficientPolynomial  [Fintype n] [DecidableEq n]
    (k : ℕ) : MvPolynomial (n × n) ℝ :=
  PowerSeries.coeff k (variableKernelSeries lo hi (n := n)).det
end


theorem determinantCoefficientPolynomial_totalDegree {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (k : ℕ) :
    (determinantCoefficientPolynomial lo hi (n := n) k).totalDegree ≤ k := by
  apply determinant_coefficient_totalDegree_le
  intro i j t
  simp only [variableKernelSeries, PowerSeries.coeff_mk]
  grind only [matrixEntryPolynomial_degree, kernelCoefficientPolynomial_natDegree]

/-- The actual matrix kernel as a matrix of formal real power series. -/
def kernelSeries (lo hi : ℝ) {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) : Matrix n n (PowerSeries ℝ) := fun i j =>
  PowerSeries.mk (fun k => (Polynomial.aeval M (kernelCoefficientPolynomial lo hi k)) i j)

section
variable {n : Type*} [Fintype n] [DecidableEq n] (lo hi : ℝ) (M : Matrix n n ℝ)

/-- Evaluation of all matrix variables produces the actual kernel entry series. -/
theorem variableKernelSeries_map_eval  :
    (PowerSeries.map (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij : n × n => M ij.1 ij.2))).mapMatrix
      (variableKernelSeries lo hi (n := n)) = kernelSeries lo hi M := by
  ext i j k
  change PowerSeries.coeff k ((PowerSeries.map
    (MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij : n × n => M ij.1 ij.2)))
      (PowerSeries.mk (fun t => matrixEntryPolynomial (kernelCoefficientPolynomial lo hi t) i j))) = _
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]
  change MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2)
    (matrixEntryPolynomial (kernelCoefficientPolynomial lo hi k) i j) = _
  simp only [kernelSeries, PowerSeries.coeff_mk]
  exact matrixEntryPolynomial_eval _ M i j

/-- Each polynomial coefficient evaluates to the kth coefficient of the actual kernel determinant. -/
theorem determinantCoefficientPolynomial_eval  (k : ℕ) :
    MvPolynomial.eval (fun ij : n × n => M ij.1 ij.2)
      (determinantCoefficientPolynomial lo hi (n := n) k) =
      PowerSeries.coeff k (kernelSeries lo hi M).det := by
  let φ := MvPolynomial.eval₂Hom (RingHom.id ℝ) (fun ij : n × n => M ij.1 ij.2)
  have he := congrArg (fun f : PowerSeries ℝ => PowerSeries.coeff k f)
    ((PowerSeries.map φ).map_det (variableKernelSeries lo hi (n := n)))
  rw [variableKernelSeries_map_eval] at he
  rw [PowerSeries.coeff_map] at he
  exact he
end


/-- Scalar series corresponding to one eigenvalue of the reciprocal kernel. -/
def scalarKernelSeries lo hi x  :=
  PowerSeries.mk (fun k => (kernelCoefficientPolynomial lo hi k).eval x)

section
variable {n : Type*}

private theorem aeval_diagonal  [Fintype n] [DecidableEq n]
    (q : ℝ[X]) (d : n → ℝ) :
    Polynomial.aeval (Matrix.diagonal d) q = Matrix.diagonal (fun i => q.eval (d i)) := by
  change Polynomial.aeval ((Matrix.diagonalAlgHom ℝ) d) q = _
  rw [Polynomial.aeval_algHom_apply, Polynomial.aeval_pi_apply]
  rfl

def coefficientMatrix  (k : ℕ) (M : Matrix n n (PowerSeries ℝ)) :
    Matrix n n ℝ := fun i j => PowerSeries.coeff k (M i j)

section
variable [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (M : Matrix n n (PowerSeries ℝ)) (k : ℕ)

theorem coefficientMatrix_constant_mul   :
    coefficientMatrix k ((PowerSeries.C.mapMatrix A) * M) = A * coefficientMatrix k M := by
  ext i j
  simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_C_mul]

theorem coefficientMatrix_mul_constant   :
    coefficientMatrix k (M * (PowerSeries.C.mapMatrix A)) = coefficientMatrix k M * A := by
  ext i j
  simp [coefficientMatrix, Matrix.mul_apply, map_sum, PowerSeries.coeff_mul_C]
end


theorem coefficientMatrix_diagonal  [DecidableEq n]
    (d : n → PowerSeries ℝ) (k : ℕ) :
    coefficientMatrix k (Matrix.diagonal d) = Matrix.diagonal (fun i => PowerSeries.coeff k (d i)) := by
  ext i j
  simp only [coefficientMatrix, Matrix.diagonal_apply]
  split_ifs <;> simp

section
variable [Fintype n] [DecidableEq n] (lo hi : ℝ) (M : Matrix n n ℝ) (hM : M.IsHermitian)

/-- The actual formal matrix kernel diagonalizes in the same fixed eigenbasis as its argument. -/
theorem kernelSeries_spectral   :
    kernelSeries lo hi M =
      (PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)) *
      Matrix.diagonal (fun i => scalarKernelSeries lo hi (hM.eigenvalues i)) *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))) := by
  ext i j k
  change (coefficientMatrix k (kernelSeries lo hi M)) i j =
    (coefficientMatrix k (_ * _ * _)) i j
  rw [coefficientMatrix_mul_constant, coefficientMatrix_constant_mul, coefficientMatrix_diagonal]
  simp only [coefficientMatrix, kernelSeries, scalarKernelSeries, PowerSeries.coeff_mk]
  have hp := Polynomial.aeval_algHom_apply
    (Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hM.eigenvectorUnitary)
    (Matrix.diagonal (RCLike.ofReal ∘ hM.eigenvalues))
    (kernelCoefficientPolynomial lo hi k)
  rw [← hM.spectral_theorem, aeval_diagonal] at hp
  have hp' : Polynomial.aeval M (kernelCoefficientPolynomial lo hi k) =
      (hM.eigenvectorUnitary : Matrix n n ℝ) *
      Matrix.diagonal (fun i => (kernelCoefficientPolynomial lo hi k).eval (hM.eigenvalues i)) *
      star (hM.eigenvectorUnitary : Matrix n n ℝ) := by
    solve_by_elim []
  exact congrArg (fun A : Matrix n n ℝ => A i j) hp'

/-- The formal determinant is exactly the product of the scalar eigenvalue reciprocal series. -/
theorem kernelSeries_det_spectral   :
    (kernelSeries lo hi M).det = ∏ i, scalarKernelSeries lo hi (hM.eigenvalues i) := by
  rw [kernelSeries_spectral lo hi M hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  have hu :
      (PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)).det *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))).det = 1 := by
    rw [← Matrix.det_mul, ← map_mul]
    have hunit : (hM.eigenvectorUnitary : Matrix n n ℝ) *
      star (hM.eigenvectorUnitary : Matrix n n ℝ) = 1 :=
      Unitary.mul_star_self_of_mem hM.eigenvectorUnitary.property
    rw [hunit, map_one, Matrix.det_one]
  calc
    _ = (∏ i, scalarKernelSeries lo hi (hM.eigenvalues i)) *
      ((PowerSeries.C.mapMatrix (hM.eigenvectorUnitary : Matrix n n ℝ)).det *
      (PowerSeries.C.mapMatrix (star (hM.eigenvectorUnitary : Matrix n n ℝ))).det) := by ring
    _ = _ := by rw [hu, mul_one]
end

end


section
variable (lo hi x : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (hx : x ∈ Set.Icc lo hi)
include hlo hlt hx

/-- Scalar kernel coefficients have the same geometric bound as in the paper. -/
theorem scalarKernelSeries_coefficient_norm_le  k :
    ‖PowerSeries.coeff k (scalarKernelSeries lo hi x)‖ ≤ 2 * intervalRho lo hi ^ k := by
  have hr := intervalRho_pos lo hi hlo hlt
  have ht : |(normalizedChebyshev lo hi k).eval x| ≤ 1 := by
    rw [normalizedChebyshev_eval]
    exact chebyshev_abs_le_one _ (interval_argument_mem lo hi x hlo hlt hx) k
  simp only [scalarKernelSeries, PowerSeries.coeff_mk, kernelCoefficientPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C]
  by_cases hk : k = 0
  · subst k
    simp [normalizedChebyshev]
  · simp only [hk, ite_false, Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_pow, abs_neg,
      abs_of_pos hr]
    simp_all []

/-- Absolute summability of every scalar eigenvalue kernel. -/
theorem scalarKernelSeries_summable_norm  :
    Summable (fun k => ‖PowerSeries.coeff k (scalarKernelSeries lo hi x)‖) := by
  have hg := (summable_geometric_of_lt_one (intervalRho_pos lo hi hlo hlt).le
    (intervalRho_lt_one lo hi hlo hlt)).mul_left (2 : ℝ)
  grind only [Summable.of_nonneg_of_le, norm_nonneg, scalarKernelSeries_coefficient_norm_le]

/-- At z=1 the scalar formal kernel sums to the normalized reciprocal. -/
theorem scalarKernelSeries_tsum  :
    (∑' k, PowerSeries.coeff k (scalarKernelSeries lo hi x)) = intervalGeometricMean lo hi / x := by
  have hs := (scalarKernelSeries_summable_norm lo hi x hlo hlt hx).of_norm
  rw [hs.tsum_eq_zero_add]
  simp only [scalarKernelSeries, PowerSeries.coeff_mk, kernelCoefficientPolynomial,
    Polynomial.eval_mul, Polynomial.eval_C, Nat.add_one_ne_zero, ite_false,
    normalizedChebyshev_eval]
  norm_num only [Int.natCast_zero, Polynomial.Chebyshev.T_zero, Polynomial.eval_one,
    ite_true, one_mul]
  simp_rw [mul_assoc]
  rw [tsum_mul_left]
  exact reciprocal_real_series lo hi x hlo hlt hx
end


section
variable {R I : Type*} [NormedCommRing R]

/-- Absolute convergence is stable under the genuine finite Cauchy product. -/
theorem powerSeries_prod_summable_norm  [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries R)
    (hf : ∀ i ∈ s, Summable (fun k => ‖PowerSeries.coeff k (f i)‖)) :
    Summable (fun k => ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖) := by
  induction s using Finset.induction_on with
  | empty =>
    apply summable_of_ne_finset_zero (s := {0})
    intro k hk
    simp only [Finset.mem_singleton] at hk
    simp [PowerSeries.coeff_one, hk]
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm
      (hf a (Finset.mem_insert_self ..))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))
    convert hs using 1
    funext k
    rw [PowerSeries.coeff_mul]

/-- The sum of the coefficients of a finite product is the product of their sums. -/
theorem powerSeries_prod_tsum  [CompleteSpace R] [DecidableEq I]
    (s : Finset I) (f : I → PowerSeries R)
    (hf : ∀ i ∈ s, Summable (fun k => ‖PowerSeries.coeff k (f i)‖)) :
    (∑' k, PowerSeries.coeff k (∏ i ∈ s, f i)) = ∏ i ∈ s, ∑' k, PowerSeries.coeff k (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [PowerSeries.coeff_one]
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
    · simp_all [powerSeries_prod_summable_norm]
end


section
variable {n : Type*} [Fintype n] [DecidableEq n] (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi) (M : Matrix n n ℝ) (hM : M.IsHermitian) (hSpec : spectrum ℝ M ⊆ Set.Icc lo hi)
include hlo hlt hM hSpec

/-- Absolute convergence of the actual formal determinant coefficients. -/
theorem kernelSeries_det_summable_norm  :
    Summable (fun k => ‖PowerSeries.coeff k (kernelSeries lo hi M).det‖) := by
  rw [kernelSeries_det_spectral lo hi M hM]
  apply powerSeries_prod_summable_norm
  intro i _
  exact scalarKernelSeries_summable_norm lo hi _ hlo hlt
    (hSpec (hM.eigenvalues_mem_spectrum_real i))

/-- The actual determinant series sums to the normalized determinant reciprocal. -/
theorem kernelSeries_det_tsum  :
    (∑' k, PowerSeries.coeff k (kernelSeries lo hi M).det) =
      intervalGeometricMean lo hi ^ Fintype.card n / M.det := by
  rw [kernelSeries_det_spectral lo hi M hM, powerSeries_prod_tsum]
  · simp_rw [scalarKernelSeries_tsum lo hi _ hlo hlt
      (hSpec (hM.eigenvalues_mem_spectrum_real _))]
    rw [Finset.prod_div_distrib]
    simp only [Finset.prod_const, Finset.card_univ]
    rw [hM.det_eq_prod_eigenvalues]
    rfl
  · intro i _
    exact scalarKernelSeries_summable_norm lo hi _ hlo hlt
      (hSpec (hM.eigenvalues_mem_spectrum_real i))
end


end RoughRegime.MatrixDeterminant
