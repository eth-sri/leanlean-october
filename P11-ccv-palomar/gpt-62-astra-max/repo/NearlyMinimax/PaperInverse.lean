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
variable {a b : ℝ} (ha : 0 < a) (hab : a < b)
include ha hab

/-- The inverse-series convergence ratio equals `exp(-τ)`. -/
theorem inverse_ratio_exterior_exponent :
    intervalRho a b = Real.exp (-intervalExteriorTau a b) := (exp_neg_exteriorTau ha hab).symm

end

/-- A positive constant independent of truncation degree. -/
def reciprocalErrorConstant (a b : ℝ) : ℝ :=
  2 / intervalGeometricMean a b * intervalRho a b / (1 - intervalRho a b)

open RoughRegime.CombinedPolynomial RoughRegime.CombinedAnalytic

/-- The entry-variable type for the current matrix and its single parent. -/
abbrev parentInverseVariables (r : ℕ) := Variables r (fun _ : Fin 1 => r)

section
variable {r : ℕ} (a b : ℝ) (A C : Matrix (Fin r) (Fin r) ℝ) (m : ℕ)

/-- Exact free-entry polynomial implementing the manuscript's single-parent truncation. -/
def parentInverseEntryPolynomial {r : ℕ} (m : ℕ) (i j : Fin r) :
    MvPolynomial (parentInverseVariables r) ℝ :=
  truncationEntryPolynomial (fun _ => r) a b i j m

/-- Evaluating the free-entry polynomials gives `P_m(A,C)`. -/
def parentInversePolynomial : Matrix (Fin r) (Fin r) ℝ :=
  truncationMatrix a b A (fun _ : Fin 1 => C) m

/-- Degree at most `m` is proved in all the free current and parent matrix entries. -/
theorem parentInverseEntryPolynomial_degree (r m : ℕ) (i j : Fin r) :
    (parentInverseEntryPolynomial a b m i j).totalDegree ≤ m :=
  truncationEntryPolynomial_degree (fun _ => r) a b i j m

/-- A finite positive constant independent of matrix entries and truncation degree. -/
def parentInverseErrorConstant (r : ℕ) : ℝ :=
  2 ^ (r + 1) * (intervalGeometricMean a b ^ (r + 1))⁻¹ *
    ∑' k, (k + 1 : ℕ) ^ r * intervalRho a b ^ k

theorem parentInverseErrorConstant_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) (r : ℕ) :
    0 < parentInverseErrorConstant a b r := by
  have hr := intervalRho_pos a b ha hab
  have hr1 := intervalRho_lt_one a b ha hab
  have hg  :=
    Real.sqrt_pos.mpr (mul_pos ha (ha.trans hab))
  have hs := RoughRegime.SeriesBounds.weighted_geometric_summable r (intervalRho a b) hr hr1
  have ht : 0 < ∑' k, (k + 1 : ℕ) ^ r * intervalRho a b ^ k := by
    apply hs.tsum_pos (fun k => by positivity) 0
    simp
  unfold parentInverseErrorConstant
  positivity

/-- The inverse/determinant approximation bound of (U4-approx), for symmetric spectral matrices. -/
theorem parent_inverse_polynomial_error [NeZero r]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {A C : Matrix (Fin r) (Fin r) ℝ} (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b) (m : ℕ) :
    ‖C.det⁻¹ • A⁻¹ - parentInversePolynomial a b A C m‖ ≤
      parentInverseErrorConstant a b r * (m + 1 : ℕ) ^ r *
        Real.exp (-m * intervalExteriorTau a b) := by
  have h := matrix_determinant_truncation_error ha hab hA hSpecA (fun _ : Fin 1 => C) (fun _ => hC) (fun _ => hSpecC) m
  simp only [Fin.sum_univ_one, Fin.prod_univ_one] at h
  apply h.trans_eq
  rw [(by rw [inverse_ratio_exterior_exponent ha hab, ← Real.exp_nat_mul]; ring : intervalRho a b ^ m = Real.exp (-↑m * intervalExteriorTau a b))]
  unfold parentInverseErrorConstant
  ring

end

section
variable {n : Type*} [Fintype n] [DecidableEq n] (Q : (Matrix n n ℝ)ˣ)

/-- Scalar-matrix conjugation as an algebra homomorphism. -/
def matrixSimilarity : Matrix n n ℝ →ₐ[ℝ] Matrix n n ℝ where
  toFun A := Q * A * (↑Q⁻¹)
  map_one' := by simp
  map_mul' A B := by simp [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one]
    simp

/-- Every matrix polynomial commutes with similarity. -/
theorem aeval_matrixSimilarity (A : Matrix n n ℝ) (P : ℝ[X]) :
    Polynomial.aeval (matrixSimilarity Q A) P = matrixSimilarity Q (Polynomial.aeval A P) := Polynomial.aeval_algHom_apply (matrixSimilarity Q) A P

/-- The operator norm under similarity gains only its condition-number factor. -/
theorem matrixSimilarity_norm_le (A : Matrix n n ℝ) :
    ‖matrixSimilarity Q A‖ ≤ ‖(Q : Matrix n n ℝ)‖ * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ * ‖A‖ := by
  calc
    _ ≤ _ := norm_mul_le _ _
    _ ≤ _ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by ring

/-- Matrix inversion commutes with similarity, including singular matrices. -/
theorem matrixSimilarity_inv (A : Matrix n n ℝ) :
    (matrixSimilarity Q A)⁻¹ = matrixSimilarity Q A⁻¹ := by
  change (Q * A * (↑Q⁻¹ : Matrix n n ℝ))⁻¹ =
    Q * A⁻¹ * _
  simp [Matrix.mul_inv_rev, ← Matrix.coe_units_inv, inv_inv, Matrix.mul_assoc]

end

open RoughRegime.MatrixDeterminant

section
variable {n : Type*} [Fintype n] [DecidableEq n] (a b : ℝ) (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ)

private theorem kernelSeries_coefficient (k : ℕ) :
    coefficientMatrix k (kernelSeries a b A) =
      Polynomial.aeval A (kernelCoefficientPolynomial a b k) := by
  ext i j
  simp [coefficientMatrix, kernelSeries]

/-- The reciprocal kernel formal series commutes with arbitrary invertible similarity. -/
theorem kernelSeries_matrixSimilarity :
    kernelSeries a b (matrixSimilarity Q A) =
      PowerSeries.C.mapMatrix Q * kernelSeries a b A *
        PowerSeries.C.mapMatrix (↑Q⁻¹) := by
  ext i j k
  change (coefficientMatrix k (kernelSeries a b (matrixSimilarity Q A))) i j =
    (coefficientMatrix k (_ * _ * _)) i j
  rw [coefficientMatrix_mul_constant, coefficientMatrix_constant_mul]
  rw [kernelSeries_coefficient, kernelSeries_coefficient]
  exact congrArg (fun M => M i j)
    (aeval_matrixSimilarity Q A (kernelCoefficientPolynomial a b k))

/-- The parent reciprocal determinant formal series is similarity invariant. -/
theorem kernelSeries_det_matrixSimilarity :
    (kernelSeries a b (matrixSimilarity Q A)).det = (kernelSeries a b A).det := by
  rw [kernelSeries_matrixSimilarity]
  have h := Matrix.det_units_conj
    (Units.map PowerSeries.C.mapMatrix.toMonoidHom Q)
    (kernelSeries a b A)
  simpa using h

end

section
variable {r : ℕ} (a b : ℝ) (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) (A C : Matrix (Fin r) (Fin r) ℝ)

private theorem matrixSeries_kernel_matrixSimilarity :
    matrixSeries (kernelSeries a b (matrixSimilarity Q A)) =
      PowerSeries.map (matrixSimilarity Q).toRingHom (matrixSeries (kernelSeries a b A)) := by
  apply PowerSeries.ext
  solve_by_elim [aeval_matrixSimilarity]

private theorem matrixSimilarity_scalar {n : Type*} [Fintype n] [DecidableEq n]
    (Q : (Matrix n n ℝ)ˣ) (x : ℝ) :
    matrixSimilarity Q (Matrix.scalar n x) = Matrix.scalar n x := (matrixSimilarity Q).commutes x

private theorem combinedSeries_parent_matrixSimilarity :
    combinedSeries a b (matrixSimilarity Q A) (fun _ : Fin 1 => matrixSimilarity R C) =
      PowerSeries.map (matrixSimilarity Q).toRingHom (combinedSeries a b A (fun _ : Fin 1 => C)) := by
  rw [combinedSeries, combinedSeries, map_mul]
  rw [matrixSeries_kernel_matrixSimilarity]
  simp [Fin.prod_univ_one, kernelSeries_det_matrixSimilarity]
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
  simp_rw [combinedSeries_parent_matrixSimilarity, PowerSeries.coeff_map]
  simp

/-- (U4-approx) for arbitrary matrices similar to symmetric spectral matrices, with condition gain `χ`. -/
theorem parent_inverse_similar_error [NeZero r]
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {A C : Matrix (Fin r) (Fin r) ℝ} (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hSpecA : spectrum ℝ A ⊆ Set.Icc a b) (hSpecC : spectrum ℝ C ⊆ Set.Icc a b)
    (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) {χ : ℝ}
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (m : ℕ) :
    ‖(matrixSimilarity R C).det⁻¹ • (matrixSimilarity Q A)⁻¹ -
      parentInversePolynomial a b (matrixSimilarity Q A) (matrixSimilarity R C) m‖ ≤
        χ * parentInverseErrorConstant a b r * (m + 1 : ℕ) ^ r *
          Real.exp (-m * intervalExteriorTau a b) := by
  have hdet : (matrixSimilarity R C).det = C.det := Matrix.det_units_conj R C
  rw [hdet, matrixSimilarity_inv, parentInversePolynomial_matrixSimilarity, ← map_smul, ← map_sub]
  have hχ0  := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ
  apply (matrixSimilarity_norm_le Q _).trans
  apply (mul_le_mul_of_nonneg_right hχ (norm_nonneg _)).trans
  apply (mul_le_mul_of_nonneg_left (parent_inverse_polynomial_error ha hab hA hC hSpecA hSpecC m) hχ0).trans_eq
  ring

end

section
variable {n : Type*} [Fintype n] [DecidableEq n] (G C T : Matrix n n ℝ) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {A : Matrix n n ℝ} (hA : A.IsHermitian) (hSpec : spectrum ℝ A ⊆ Set.Icc a b)
    (hG : G.det ≠ 0) (hC : C.det ≠ 0) (β βminus : n → ℝ)

/-- The determinant-cleared fitted increment numerator from (Udef-increment). -/
def incrementNumerator : n → ℝ :=
  C.det • β - G.mulVec (T.mulVec (C.adjugate.mulVec βminus))

include hG hC in
/-- The adjugate identity proves (U5-identity) for every invertible current and parent matrix. -/
theorem incrementNumerator_identity :
    C.det⁻¹ • G⁻¹.mulVec (incrementNumerator G C T β βminus) =
      G⁻¹.mulVec β - T.mulVec (C⁻¹.mulVec βminus) := by
  have hunitG  := isUnit_iff_ne_zero.mpr hG
  rw [incrementNumerator, Matrix.mulVec_sub, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul G hunitG, Matrix.one_mulVec,
    smul_sub, smul_smul, inv_mul_cancel₀ hC, one_smul]
  simp [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_mulVec, Matrix.mulVec_smul]

include hG hC in
/-- The cleared numerator preserves the increment cancellation before approximation. -/
theorem incrementNumerator_factorization :
    incrementNumerator G C T β βminus =
      C.det • G.mulVec (G⁻¹.mulVec β - T.mulVec (C⁻¹.mulVec βminus)) := by
  have hunitG  := isUnit_iff_ne_zero.mpr hG
  have hid := incrementNumerator_identity G C T hG hC β βminus
  have h := congrArg (fun v => C.det • G.mulVec v) hid
  simpa only [Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hC, one_smul,
    Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G hunitG, Matrix.one_mulVec] using h

include ha hA hSpec in
/-- Positive-interval spectrum proves nonzero determinant, without an invertibility hypothesis. -/
theorem spectral_det_ne_zero : A.det ≠ 0 := by
  rw [hA.det_eq_prod_eigenvalues]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact ne_of_gt (ha.trans_le (hSpec (hA.eigenvalues_mem_spectrum_real i)).1)

include ha hab hA hSpec in
/-- A Hermitian matrix with positive interval spectrum has operator norm at most the upper endpoint. -/
theorem spectral_norm_le : ‖A‖ ≤ b := by
  have hs  := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  rw [← cfc_id ℝ A hs]
  apply norm_cfc_le (by linarith)
  intro x hx
  have h := hSpec hx
  simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg (ha.le.trans h.1)] using h.2

include ha hab hA hSpec in
/-- The determinant of a positive spectral matrix is bounded by the endpoint to the dimension. -/
theorem spectral_det_abs_le : |A.det| ≤ b ^ Fintype.card n := by
  rw [hA.det_eq_prod_eigenvalues, Finset.abs_prod]
  calc
    ∏ i, |hA.eigenvalues i| ≤ ∏ _i, b := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact abs_nonneg _
      · intro i hi
        have h := hSpec (hA.eigenvalues_mem_spectrum_real i)
        grind
    _ = _ := by simp

end

variable {r : ℕ} [NeZero r] {a b : ℝ} (ha : 0 < a) (hab : a < b) (A C T : Matrix (Fin r) (Fin r) ℝ)
    (hA : A.IsHermitian) (hC : C.IsHermitian) (hSpecA : spectrum ℝ A ⊆ Set.Icc a b)
    (hSpecC : spectrum ℝ C ⊆ Set.Icc a b) (Q R : (Matrix (Fin r) (Fin r) ℝ)ˣ) {χ : ℝ}
    (hχ : ‖(Q : Matrix (Fin r) (Fin r) ℝ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ)
    (β βminus : Fin r → ℝ)
include hA hC hSpecA hSpecC ha hab hχ

/-- Determinant clearing preserves the small increment with the precise spectral-size factor. -/
theorem increment_numerator_norm_le :
    let G := matrixSimilarity Q A
    let Cminus := matrixSimilarity R C
    ‖(EuclideanSpace.equiv (Fin r) ℝ).symm (incrementNumerator G Cminus T β βminus)‖ ≤
      χ * b ^ (r + 1) * ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
        (G⁻¹.mulVec β - T.mulVec (Cminus⁻¹.mulVec βminus))‖ := by
  let G := matrixSimilarity Q A
  let Cminus := matrixSimilarity R C
  let δ := G⁻¹.mulVec β - T.mulVec (Cminus⁻¹.mulVec βminus)
  have hG : G.det ≠ 0 := by
    rw [show G.det = A.det from Matrix.det_units_conj Q A]
    exact spectral_det_ne_zero ha hA hSpecA
  have hCm : Cminus.det ≠ 0 := by
    rw [show Cminus.det = C.det from Matrix.det_units_conj R C]
    exact spectral_det_ne_zero ha hC hSpecC
  have hχ0  := (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hχ
  have hb  := ha.trans hab
  have hnG : ‖G‖ ≤ χ * b := by
    apply (matrixSimilarity_norm_le Q A).trans
    apply (mul_le_mul_of_nonneg_right hχ (norm_nonneg A)).trans
    exact mul_le_mul_of_nonneg_left (spectral_norm_le ha hab hA hSpecA) hχ0
  have hdC : |Cminus.det| ≤ b ^ r := by
    rw [show Cminus.det = C.det from Matrix.det_units_conj R C]
    simpa using spectral_det_abs_le ha hab hC hSpecC
  change _ ≤ _
  rw [incrementNumerator_factorization G Cminus T hG hCm]
  change ‖Cminus.det • (EuclideanSpace.equiv (Fin r) ℝ).symm (G.mulVec δ)‖ ≤ _
  rw [norm_smul, Real.norm_eq_abs]
  have hv := G.l2_opNorm_mulVec ((EuclideanSpace.equiv (Fin r) ℝ).symm δ)
  calc
    _ ≤
        b ^ r * (‖G‖ * ‖(EuclideanSpace.equiv (Fin r) ℝ).symm δ‖) :=
      by bound
    _ ≤ _ :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnG (norm_nonneg _)) (by positivity)
    _ = _ := by ring

/-- Applying any inverse/determinant approximation to the cleared numerator incurs only
its operator error times the numerator norm. This is the analytic step behind (U5-error). -/
theorem increment_polynomial_error (m : ℕ) :
    let G := matrixSimilarity Q A
    let Cminus := matrixSimilarity R C
    let N := incrementNumerator G Cminus T β βminus
    ‖(EuclideanSpace.equiv (Fin r) ℝ).symm
      ((parentInversePolynomial a b G Cminus m).mulVec N -
        (G⁻¹.mulVec β - T.mulVec (Cminus⁻¹.mulVec βminus)))‖ ≤
      (χ * parentInverseErrorConstant a b r * (m + 1 : ℕ) ^ r *
        Real.exp (-m * intervalExteriorTau a b)) *
        ‖(EuclideanSpace.equiv (Fin r) ℝ).symm N‖ := by
  let G := matrixSimilarity Q A
  let Cminus := matrixSimilarity R C
  let N := incrementNumerator G Cminus T β βminus
  have hG : G.det ≠ 0 := by
    rw [show G.det = A.det from Matrix.det_units_conj Q A]
    exact spectral_det_ne_zero ha hA hSpecA
  have hCm : Cminus.det ≠ 0 := by
    rw [show Cminus.det = C.det from Matrix.det_units_conj R C]
    exact spectral_det_ne_zero ha hC hSpecC
  have hid := incrementNumerator_identity G Cminus T hG hCm β βminus
  change _ ≤ _
  rw [← hid, ← Matrix.smul_mulVec, ← Matrix.sub_mulVec]
  have hn := (parentInversePolynomial a b G Cminus m - Cminus.det⁻¹ • G⁻¹).l2_opNorm_mulVec
    ((EuclideanSpace.equiv (Fin r) ℝ).symm N)
  apply hn.trans
  rw [norm_sub_rev]
  exact mul_le_mul_of_nonneg_right
    (parent_inverse_similar_error ha hab hA hC hSpecA hSpecC Q R hχ m)
    (norm_nonneg _)

end NearlyMinimax
