module

public import RoughRegime.MatrixKernel
public import RoughRegime.CombinedPolynomial

@[expose] public section

/-! Operator norm and convergence bridge for the full matrix/determinant
combined-index reciprocal truncation of Lemma 5(a). -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator

namespace RoughRegime.CombinedAnalytic
open RoughRegime.MatrixDeterminant RoughRegime.MatrixKernel RoughRegime.SeriesBounds
open RoughRegime.Upper RoughRegime.CombinedPolynomial

/-- Convert entrywise scalar formal series to a matrix-valued formal series. -/
def matrixSeries {n : Type*} [Fintype n] [DecidableEq n] (K : Matrix n n (PowerSeries ℝ)) : PowerSeries (Matrix n n ℝ) :=
  PowerSeries.mk (fun k => coefficientMatrix k K)

section
variable {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n (PowerSeries ℝ))

/-- Entrywise multiplication by a scalar series is matrix multiplication by its scalar matrix. -/
theorem matrixSeries_scalar_mul (g : PowerSeries ℝ) :
    matrixSeries (fun i j => K i j * g) =
      matrixSeries K * PowerSeries.map (Matrix.scalar n) g := by
  ext k i j
  simp only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, PowerSeries.coeff_mul,
    PowerSeries.coeff_map, Matrix.sum_apply, Matrix.scalar_apply, Matrix.mul_diagonal]

end

section
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A scalar coefficient embedded as a scalar matrix has the same operator norm. -/
theorem scalarMatrix_coefficient_norm [Nonempty n]
    (g : PowerSeries ℝ) (k : ℕ) :
    ‖PowerSeries.coeff k (PowerSeries.map (Matrix.scalar n) g)‖ = ‖PowerSeries.coeff k g‖ := by
  simp

end

/-- The genuine matrix/determinant combined generating series. -/
def combinedSeries {N n0 : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) :
    PowerSeries (Matrix (Fin n0) (Fin n0) ℝ) :=
  matrixSeries (kernelSeries lo hi M0) *
    PowerSeries.map (Matrix.scalar (Fin n0)) (∏ i, (kernelSeries lo hi (M i)).det)

/-- The matrix-valued coefficients evaluate exactly the entry polynomials. -/
theorem combinedSeries_coefficient_entry {N n0 : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (a b : Fin n0) (k : ℕ) :
    (PowerSeries.coeff k (combinedSeries lo hi M0 M)) a b =
      MvPolynomial.eval (entryValuation M0 M)
        (combinedCoefficientPolynomial n0 dims lo hi a b k) := by
  rw [combinedSeries, ← matrixSeries_scalar_mul]
  simpa only [matrixSeries, PowerSeries.coeff_mk, coefficientMatrix, Algebra.algebraMap_self,
    MvPolynomial.eval₂_id] using (combinedCoefficientPolynomial_eval n0 dims lo hi M0 M a b k).symm

/-- Flatten all reciprocal eigenvalue factors, including zero-dimensional determinant blocks. -/
def eigenvalueSeriesList {N : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) : List (PowerSeries ℝ) :=
  (Finset.univ : Finset ((i : Fin N) × Fin (dims i))).toList.map
    (fun ij => scalarKernelSeries lo hi ((hM ij.1).eigenvalues ij.2))

section
variable {N : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian)

lemma eigenvalueSeriesList_length :
    (eigenvalueSeriesList lo hi M hM).length = ∑ i, dims i := by
  simp only [eigenvalueSeriesList, List.length_map, Finset.length_toList, Finset.card_univ,
    Fintype.card_sigma, Fintype.card_fin]

lemma eigenvalueSeriesList_prod :
    (eigenvalueSeriesList lo hi M hM).prod = ∏ i, (kernelSeries lo hi (M i)).det := by
  rw [eigenvalueSeriesList, Finset.prod_map_toList, Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro i _
  exact (kernelSeries_det_spectral lo hi (M i) (hM i)).symm

end

@[simp] theorem matrixSeries_kernel_coeff {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℝ) (k : ℕ) :
    PowerSeries.coeff k (matrixSeries (kernelSeries lo hi M)) = matrixKernelCoefficient lo hi M k := by
  ext i j
  simp [matrixSeries, coefficientMatrix, kernelSeries, matrixKernelCoefficient]

section
variable {N n0 : ℕ}

/-- Full factor-count coefficient bound of Lemma 5(a), in the actual operator norm. -/
theorem combinedSeries_coefficient_norm_le [Nonempty (Fin n0)] {dims : Fin N → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ) (hM0 : M0.IsHermitian)
    (hSpec0 : spectrum ℝ M0 ⊆ Set.Icc lo hi)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) (hSpec : ∀ i, spectrum ℝ (M i) ⊆ Set.Icc lo hi)
    (k : ℕ) :
    ‖PowerSeries.coeff k (combinedSeries lo hi M0 M)‖ ≤
      2 ^ ((∑ i, dims i) + 1) * ((k + 1 : ℕ) : ℝ) ^ (∑ i, dims i) * intervalRho lo hi ^ k := by
  let f := matrixSeries (kernelSeries lo hi M0)
  let g := PowerSeries.map (Matrix.scalar (Fin n0) : ℝ →+* Matrix (Fin n0) (Fin n0) ℝ)
  rw [combinedSeries, ← eigenvalueSeriesList_prod lo hi M hM, map_list_prod]
  have hg (s : PowerSeries (Matrix (Fin n0) (Fin n0) ℝ))
      (hs : s ∈ (eigenvalueSeriesList lo hi M hM).map g) (j : ℕ) :
      ‖PowerSeries.coeff j s‖ ≤ 2 * intervalRho lo hi ^ j := by
    rcases List.mem_map.mp hs with ⟨t, ht, rfl⟩
    unfold eigenvalueSeriesList at ht
    rcases List.mem_map.mp ht with ⟨ij, _, rfl⟩
    simpa only [g, scalarMatrix_coefficient_norm] using scalarKernelSeries_coefficient_norm_le lo hi _ hlo hlt
      (hSpec ij.1 ((hM ij.1).eigenvalues_mem_spectrum_real ij.2)) j
  have h := coeff_mul_list_geometric_bound f ((eigenvalueSeriesList lo hi M hM).map g)
    (intervalRho lo hi) 2 2 (intervalRho_pos lo hi hlo hlt) (by norm_num) (by norm_num)
    (fun j => by simpa [f] using matrixKernelCoefficient_norm_le lo hi hlo hlt M0 hM0 hSpec0 j) hg k
  simpa only [f, g, List.length_map, eigenvalueSeriesList_length, pow_succ, mul_assoc, mul_left_comm,
    mul_comm] using h

end

/-- Scalar matrices commute with coefficient summation. -/
theorem scalarMatrix_tsum {n : Type*} [Fintype n] [DecidableEq n]
    (f : ℕ → ℝ) (hf : Summable f) :
    (∑' k, (Matrix.scalar n) (f k)) = (Matrix.scalar n) (∑' k, f k) := by
  have hc : Continuous (Matrix.scalar n : ℝ → Matrix n n ℝ) := (continuous_pi (fun _ => continuous_id)).matrix_diagonal
  exact (hf.hasSum.map (Matrix.scalar n) hc).tsum_eq

/-- The sum of all determinant factors is the common normalization divided by the determinant product. -/
theorem determinantProduct_tsum {N : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) (hSpec : ∀ i, spectrum ℝ (M i) ⊆ Set.Icc lo hi) :
    (∑' k, PowerSeries.coeff k (∏ i, (kernelSeries lo hi (M i)).det)) =
      intervalGeometricMean lo hi ^ (∑ i, dims i) / ∏ i, (M i).det := by
  rw [powerSeries_prod_tsum]
  · simp_rw [kernelSeries_det_tsum lo hi hlo hlt _ (hM _) (hSpec _), Fintype.card_fin]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]
  · intro i _
    solve_by_elim [kernelSeries_det_summable_norm]

/-- The actual combined generating series sums to ḡ^(ν'+1) times the inverse/determinant target. -/
theorem combinedSeries_tsum {N n0 : ℕ} [Nonempty (Fin n0)] {dims : Fin N → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ) (hM0 : M0.IsHermitian)
    (hSpec0 : spectrum ℝ M0 ⊆ Set.Icc lo hi)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) (hSpec : ∀ i, spectrum ℝ (M i) ⊆ Set.Icc lo hi) :
    (∑' k, PowerSeries.coeff k (combinedSeries lo hi M0 M)) =
      (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1) / ∏ i, (M i).det) • M0⁻¹ := by
  let D := ∏ i, (kernelSeries lo hi (M i)).det
  have hDn := by
    exact powerSeries_prod_summable_norm Finset.univ _ (fun i _ =>
      kernelSeries_det_summable_norm lo hi hlo hlt (M i) (hM i) (hSpec i))
  have hDmn : Summable (fun k => ‖PowerSeries.coeff k
      (PowerSeries.map (Matrix.scalar (Fin n0)) D)‖) := by
    simpa only [scalarMatrix_coefficient_norm] using hDn
  rw [combinedSeries, coeff_mul_tsum _ _ (by
    simpa using matrixKernelCoefficient_summable_norm lo hi hlo hlt M0 hM0 hSpec0) hDmn]
  simp only [matrixSeries_kernel_coeff, matrixKernelCoefficient_tsum lo hi hlo hlt M0 hM0 hSpec0]
  simp only [PowerSeries.coeff_map]
  rw [scalarMatrix_tsum _ hDn.of_norm, determinantProduct_tsum lo hi hlo hlt M hM hSpec, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal, smul_smul] <;> ring

/-- Finite matrix polynomial with the exact combined-index truncation and normalization. -/
def truncationMatrix {N n0 : ℕ} {dims : Fin N → ℕ}
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (m : ℕ) :
    Matrix (Fin n0) (Fin n0) ℝ :=
  fun a b => MvPolynomial.eval (entryValuation M0 M) (truncationEntryPolynomial n0 dims lo hi a b m)

section
variable {N n0 : ℕ}

/-- Exact identification of the concrete entry polynomials with the formal combined-index truncation. -/
theorem truncationMatrix_eq_scaled_sum {dims : Fin N → ℕ}
    (lo hi : ℝ) (M0 : Matrix (Fin n0) (Fin n0) ℝ)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ) (m : ℕ) :
    truncationMatrix lo hi M0 M m =
      (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ •
        ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (combinedSeries lo hi M0 M) := by
  ext a b
  simp only [truncationMatrix, truncationEntryPolynomial, Matrix.smul_apply,
    smul_eq_mul, Matrix.sum_apply, combinedSeries_coefficient_entry, map_sum, map_mul, MvPolynomial.eval_C]

/-- Full Lemma 5(a): the arbitrary determinant-product approximation error in operator norm.
Together with `truncationEntryPolynomial_degree`, this proves the matrix polynomial assertion. -/
theorem matrix_determinant_truncation_error [Nonempty (Fin n0)] {dims : Fin N → ℕ}
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (M0 : Matrix (Fin n0) (Fin n0) ℝ) (hM0 : M0.IsHermitian)
    (hSpec0 : spectrum ℝ M0 ⊆ Set.Icc lo hi)
    (M : (i : Fin N) → Matrix (Fin (dims i)) (Fin (dims i)) ℝ)
    (hM : ∀ i, (M i).IsHermitian) (hSpec : ∀ i, spectrum ℝ (M i) ⊆ Set.Icc lo hi) (m : ℕ) :
    ‖(∏ i, (M i).det)⁻¹ • M0⁻¹ - truncationMatrix lo hi M0 M m‖ ≤
      2 ^ ((∑ i, dims i) + 1) * (intervalGeometricMean lo hi ^ ((∑ i, dims i) + 1))⁻¹ *
        ((m + 1 : ℕ) : ℝ) ^ (∑ i, dims i) * intervalRho lo hi ^ m *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (∑ i, dims i) * intervalRho lo hi ^ k := by
  let ν : ℕ := ∑ i, dims i
  let α : ℝ := (intervalGeometricMean lo hi ^ (ν + 1))⁻¹
  have hg : intervalGeometricMean lo hi ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (mul_pos hlo (hlo.trans hlt)))
  have hα : 0 ≤ α := by dsimp [α, intervalGeometricMean]; positivity
  have htarget : (∏ i, (M i).det)⁻¹ • M0⁻¹ =
      α • ∑' k, PowerSeries.coeff k (combinedSeries lo hi M0 M) := by
    rw [combinedSeries_tsum lo hi hlo hlt M0 hM0 hSpec0 M hM hSpec, smul_smul, div_eq_mul_inv, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hg), one_mul]
  rw [htarget, truncationMatrix_eq_scaled_sum]
  change ‖α • _ - α • _‖ ≤ _
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
  have he := series_truncation_bound
    (fun k => PowerSeries.coeff k (combinedSeries lo hi M0 M)) ν m (intervalRho lo hi)
    (2 ^ (ν + 1)) (intervalRho_pos lo hi hlo hlt) (intervalRho_lt_one lo hi hlo hlt)
    (by positivity) (combinedSeries_coefficient_norm_le lo hi hlo hlt M0 hM0 hSpec0 M hM hSpec)
  apply (mul_le_mul_of_nonneg_left he hα).trans_eq
  ring

end

end RoughRegime.CombinedAnalytic
