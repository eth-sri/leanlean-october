module

public import NearlyMinimax.Chebyshev
public import RoughRegime.CombinedAnalytic

@[expose] public section

/-!
# Reciprocal polynomial ingredients for `upper_B.tex`

The imported algebraic and analytic reciprocal construction is specialized to
one parent determinant, exactly the product in the manuscript. Results stated
with Hermitian matrices below explicitly retain that hypothesis. The scalar
exponent bridge identifies the rate parameter with the manuscript's `τ`.
-/

noncomputable section

namespace NearlyMinimax

open Polynomial
open scoped BigOperators Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.MatrixUpper

section
variable (a b : ℝ) (ha : 0 < a) (hab : a < b)
include ha hab

/-- The inverse-series convergence ratio equals `exp(-τ)`. -/
theorem inverse_ratio_exterior_exponent :
    intervalRho a b = Real.exp (-exteriorTau ((a + b) / (b - a))) := (exp_neg_exteriorTau a b ha hab).symm

/-- Integer powers of the convergence ratio have the manuscript's exponential form. -/
theorem inverse_ratio_pow (m : ℕ) :
    intervalRho a b ^ m = Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  simp [inverse_ratio_exterior_exponent a b ha hab, ← Real.exp_nat_mul]

end

open RoughRegime.CombinedPolynomial RoughRegime.CombinedAnalytic

/-- The entry-variable type for the current matrix and its single parent. -/
abbrev parentInverseVariables (r : ℕ) := Variables r (fun _ : Fin 1 => r)

/-- Exact free-entry polynomial implementing the manuscript's single-parent truncation. -/
def parentInverseEntryPolynomial (a b : ℝ) (r m : ℕ) (i j : Fin r) :
    MvPolynomial (parentInverseVariables r) ℝ :=
  truncationEntryPolynomial r (fun _ : Fin 1 => r) a b i j m

/-- Evaluating the free-entry polynomials gives `P_m(A,C)`. -/
def parentInversePolynomial {r : ℕ} (a b : ℝ)
    (A C : Matrix (Fin r) (Fin r) ℝ) (m : ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  truncationMatrix a b A (fun _ : Fin 1 => C) m

/-- Degree at most `m` is proved in all the free current and parent matrix entries. -/
theorem parentInverseEntryPolynomial_degree (a b : ℝ) (r m : ℕ) (i j : Fin r) :
    (parentInverseEntryPolynomial a b r m i j).totalDegree ≤ m :=
  by apply truncationEntryPolynomial_degree

/-- A finite positive constant independent of matrix entries and truncation degree. -/
def parentInverseErrorConstant (a b : ℝ) (r : ℕ) : ℝ :=
  2 ^ (r + 1) * (intervalGeometricMean a b ^ (r + 1))⁻¹ *
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ r * intervalRho a b ^ k

theorem parentInverseErrorConstant_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) (r : ℕ) :
    0 < parentInverseErrorConstant a b r := by
  have hr := intervalRho_pos a b ha hab
  have hr1 := intervalRho_lt_one a b ha hab
  have hg :=
    Real.sqrt_pos.mpr (mul_pos ha (ha.trans hab))
  have hs := RoughRegime.SeriesBounds.weighted_geometric_summable r (intervalRho a b) hr hr1
  have ht : 0 < ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ r * intervalRho a b ^ k := by
    apply hs.tsum_pos (fun k => by positivity) 0
    simp
  unfold parentInverseErrorConstant
  positivity

/-- The inverse/determinant approximation bound of (U4-approx), for symmetric spectral matrices. -/
theorem parent_inverse_polynomial_error {r : ℕ} [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b) (m : ℕ) :
    ‖C.det⁻¹ • A⁻¹ - parentInversePolynomial a b A C m‖ ≤
      parentInverseErrorConstant a b r * ((m + 1 : ℕ) : ℝ) ^ r *
        Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  have h := matrix_determinant_truncation_error (N := 1) (dims := fun _ : Fin 1 => r)
    a b ha hab A hA hSpecA (fun _ : Fin 1 => C) (fun _ => hC) (fun _ => hSpecC) m
  simp only [Fin.sum_univ_one, Fin.prod_univ_one] at h
  apply h.trans_eq
  rw [inverse_ratio_pow a b ha hab m]
  unfold parentInverseErrorConstant
  ring

/-- Scalar-matrix conjugation as an algebra homomorphism. -/
def matrixSimilarity {n S : Type*} [CommRing S] [Algebra ℝ S] [Fintype n] [DecidableEq n]
    (Q : (Matrix n n S)ˣ) : Matrix n n S →ₐ[ℝ] Matrix n n S where
  toFun A := (Q : Matrix n n S) * A * (↑Q⁻¹ : Matrix n n S)
  map_one' := by simp
  map_mul' A B := by simp [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    simp_all [Algebra.algebraMap_eq_smul_one]

/-- The operator norm under similarity gains only its condition-number factor. -/
theorem matrixSimilarity_norm_le {n K : Type*} [Fintype n] [DecidableEq n] [RCLike K]
    (Q : (Matrix n n K)ˣ) (A : Matrix n n K) :
    ‖matrixSimilarity Q A‖ ≤ ‖(Q : Matrix n n K)‖ * ‖(↑Q⁻¹ : Matrix n n K)‖ * ‖A‖ := by
  calc
    _ ≤ ‖(Q : Matrix n n K) * A‖ * ‖(↑Q⁻¹ : Matrix n n K)‖ := norm_mul_le _ _
    _ ≤ (‖(Q : Matrix n n K)‖ * ‖A‖) * ‖(↑Q⁻¹ : Matrix n n K)‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by ring

section
variable {n : Type*} [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ)

/-- Every matrix polynomial commutes with similarity. -/
theorem aeval_matrixSimilarity (P : ℝ[X]) :
    Polynomial.aeval (matrixSimilarity Q A) P = matrixSimilarity Q (Polynomial.aeval A P) := by
  apply Polynomial.aeval_algHom_apply

/-- Matrix inversion commutes with similarity, including singular matrices. -/
theorem matrixSimilarity_inv :
    (matrixSimilarity Q A)⁻¹ = matrixSimilarity Q A⁻¹ := by
  change ((Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ))⁻¹ =
    (Q : Matrix n n ℝ) * A⁻¹ * (↑Q⁻¹ : Matrix n n ℝ)
  simp only [Matrix.mul_inv_rev, ← Matrix.coe_units_inv, inv_inv, Matrix.mul_assoc]

end

open RoughRegime.MatrixDeterminant

section
variable {n : Type*} [Fintype n] [DecidableEq n]
    (a b : ℝ)

private theorem kernelSeries_coefficient (A : Matrix n n ℝ) (k : ℕ) :
    coefficientMatrix k (kernelSeries a b A) =
      Polynomial.aeval A (kernelCoefficientPolynomial a b k) := by
  ext i j
  simp only [coefficientMatrix, kernelSeries, PowerSeries.coeff_mk]

section
variable (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ)

/-- The reciprocal kernel formal series commutes with arbitrary invertible similarity. -/
theorem kernelSeries_matrixSimilarity :
    kernelSeries a b (matrixSimilarity Q A) =
      PowerSeries.C.mapMatrix (Q : Matrix n n ℝ) * kernelSeries a b A *
        PowerSeries.C.mapMatrix (↑Q⁻¹ : Matrix n n ℝ) := by
  ext i j k
  change (coefficientMatrix k (kernelSeries a b (matrixSimilarity Q A))) i j =
    (coefficientMatrix k (_ * _ * _)) i j
  rw [coefficientMatrix_mul_constant, coefficientMatrix_constant_mul]
  rw [kernelSeries_coefficient, kernelSeries_coefficient]
  exact congrArg (fun M : Matrix n n ℝ => M i j)
    (aeval_matrixSimilarity Q A (kernelCoefficientPolynomial a b k))

/-- The parent reciprocal determinant formal series is similarity invariant. -/
theorem kernelSeries_det_matrixSimilarity :
    (kernelSeries a b (matrixSimilarity Q A)).det = (kernelSeries a b A).det := by
  rw [kernelSeries_matrixSimilarity]
  have h := Matrix.det_units_conj
    (Units.map (PowerSeries.C.mapMatrix : Matrix n n ℝ →+* Matrix n n (PowerSeries ℝ)).toMonoidHom Q)
    (kernelSeries a b A)
  assumption

end

end

private theorem matrixSeries_kernel_matrixSimilarity {r : ℕ}
    (a b : ℝ) (Q : (Matrix (Fin r) (Fin r) ℝ)ˣ) (A : Matrix (Fin r) (Fin r) ℝ) :
    matrixSeries (kernelSeries a b (matrixSimilarity Q A)) =
      PowerSeries.map (matrixSimilarity Q).toRingHom (matrixSeries (kernelSeries a b A)) := by
  solve_by_elim [PowerSeries.ext, aeval_matrixSimilarity]

private theorem matrixSimilarity_scalar {n : Type*} [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (x : ℝ) :
    matrixSimilarity Q (Matrix.scalar n x) = Matrix.scalar n x := (matrixSimilarity Q).commutes x

section
variable {r : ℕ}

section
variable (a b : ℝ) (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (A C : Matrix (Fin r) (Fin r) ℝ)

private theorem combinedSeries_parent_matrixSimilarity :
    combinedSeries a b (matrixSimilarity Q A) (fun _ : Fin 1 => matrixSimilarity R C) =
      PowerSeries.map (matrixSimilarity Q).toRingHom (combinedSeries a b A (fun _ : Fin 1 => C)) := by
  rw [combinedSeries, combinedSeries, map_mul]
  rw [matrixSeries_kernel_matrixSimilarity]
  simp only [Fin.prod_univ_one, kernelSeries_det_matrixSimilarity]
  congr 1
  apply PowerSeries.ext
  intro k
  exact (matrixSimilarity_scalar Q _).symm

/-- The single-parent truncation is equivariant in the current matrix and invariant in the parent. -/
theorem parentInversePolynomial_matrixSimilarity (m : ℕ) :
    parentInversePolynomial a b (matrixSimilarity Q A) (matrixSimilarity R C) m =
      matrixSimilarity Q (parentInversePolynomial a b A C m) := by
  rw [parentInversePolynomial, parentInversePolynomial,
    truncationMatrix_eq_scaled_sum, truncationMatrix_eq_scaled_sum]
  simp [combinedSeries_parent_matrixSimilarity, PowerSeries.coeff_map, map_smul, map_sum]

end

/-- (U4-approx) for arbitrary matrices similar to symmetric spectral matrices, with condition gain `χ`. -/
theorem parent_inverse_similar_error [NeZero r]
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (A C : Matrix (Fin r) (Fin r) ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (χ : ℝ)
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (m : ℕ) :
    ‖(matrixSimilarity R C).det⁻¹ • (matrixSimilarity Q A)⁻¹ -
      parentInversePolynomial a b (matrixSimilarity Q A) (matrixSimilarity R C) m‖ ≤
        χ * parentInverseErrorConstant a b r * ((m + 1 : ℕ) : ℝ) ^ r *
          Real.exp (-(m : ℝ) * exteriorTau ((a + b) / (b - a))) := by
  have hdet : (matrixSimilarity R C).det = C.det := Matrix.det_units_conj R C
  rw [hdet, matrixSimilarity_inv, parentInversePolynomial_matrixSimilarity, ← map_smul, ← map_sub]
  have hχ0 : 0 ≤ χ := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ
  apply (matrixSimilarity_norm_le Q _).trans
  apply (mul_le_mul_of_nonneg_right hχ (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (parent_inverse_polynomial_error a b ha hab A C hA hC hSpecA hSpecC m) hχ0).trans_eq
  ring

end

/-- The determinant-cleared fitted increment numerator from (Udef-increment). -/
def incrementNumerator {n : Type*} [Fintype n] [DecidableEq n]
    (G C T : Matrix n n ℝ) (β βminus : n → ℝ) : n → ℝ :=
  C.det • β - G.mulVec (T.mulVec (C.adjugate.mulVec βminus))

section
variable {n : Type*} [Fintype n] [DecidableEq n]

section
variable (G C T : Matrix n n ℝ) (hG : G.det ≠ 0) (hC : C.det ≠ 0) (β βminus : n → ℝ)
include hG hC

/-- The adjugate identity proves (U5-identity) for every invertible current and parent matrix. -/
theorem incrementNumerator_identity :
    C.det⁻¹ • G⁻¹.mulVec (incrementNumerator G C T β βminus) =
      G⁻¹.mulVec β - T.mulVec (C⁻¹.mulVec βminus) := by
  have hunitG := isUnit_iff_ne_zero.mpr hG
  rw [incrementNumerator, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hunitG, Matrix.one_mulVec,
    smul_sub, smul_smul, inv_mul_cancel₀ hC, one_smul]
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec, Matrix.mulVec_smul]

/-- The cleared numerator preserves the increment cancellation before approximation. -/
theorem incrementNumerator_factorization :
    incrementNumerator G C T β βminus =
      C.det • G.mulVec (G⁻¹.mulVec β - T.mulVec (C⁻¹.mulVec βminus)) := by
  have hunitG := isUnit_iff_ne_zero.mpr hG
  have hid := incrementNumerator_identity G C T hG hC β βminus
  have h := congrArg (fun v : n → ℝ => C.det • G.mulVec v) hid
  simpa only [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hC, one_smul,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hunitG, Matrix.one_mulVec] using h

end

section
variable (a b : ℝ) (ha : 0 < a)
include ha

/-- Positive-interval spectrum proves nonzero determinant, without an invertibility hypothesis. -/
theorem spectral_det_ne_zero (A : Matrix n n ℝ)
    (hSpec : spectrum ℝ A ⊆ Set.Icc a b) : A.det ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det, ← spectrum.zero_notMem_iff ℝ]
  exact fun h => (not_le.mpr ha) (hSpec h).1

section
variable (hab : a < b) (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hSpec : spectrum ℝ A ⊆ Set.Icc a b)
include hab hA hSpec

/-- A Hermitian matrix with positive interval spectrum has operator norm at most the upper endpoint. -/
theorem spectral_norm_le : ‖A‖ ≤ b := by
  have hs := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  rw [← cfc_id ℝ A hs]
  apply norm_cfc_le (by linarith)
  intro x hx
  have h := hSpec hx
  simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg (ha.le.trans h.1)] using h.2

/-- The determinant of a positive spectral matrix is bounded by the endpoint to the dimension. -/
theorem spectral_det_abs_le : |A.det| ≤ b ^ Fintype.card n := by
  rw [hA.det_eq_prod_eigenvalues, Finset.abs_prod]
  calc
    ∏ i, |hA.eigenvalues i| ≤ ∏ _i : n, b := by
      apply Finset.prod_le_prod₀
      · simp_all
      · intro i hi
        have h := hSpec (hA.eigenvalues_mem_spectrum_real i)
        grind
    _ = _ := by simp

end

end

end

end NearlyMinimax
