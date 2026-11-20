module

public import NearlyMinimax.PaperIncrement
public import RoughRegime.ComplexDerivativeBridge

@[expose] public section

/-! Degree-independent complex-neighborhood bounds for the actual reciprocal polynomials. -/

noncomputable section
namespace NearlyMinimax
open scoped BigOperators
open Polynomial

section ChebyshevPerturbation
variable {R : Type*} [Ring R] [Algebra ℝ R]

variable (x : R) (f : ℕ → R) (y : R) (n : ℕ)

def matrixChebyshevT : R := aeval x (Chebyshev.T ℝ n)
def matrixChebyshevU (n : ℤ) : R := aeval x (Chebyshev.U ℝ n)

theorem matrixChebyshevT_recurrence :
    matrixChebyshevT x (n + 2) = 2 * x * matrixChebyshevT x (n + 1) - matrixChebyshevT x n := by
  simp [matrixChebyshevT, map_ofNat]

theorem matrixChebyshevU_recurrence (n : ℤ) :
    matrixChebyshevU x (n + 1) = 2 * x * matrixChebyshevU x n - matrixChebyshevU x (n - 1) := by
  unfold matrixChebyshevU
  rw [Chebyshev.U_add_one]
  simp [map_ofNat]

/-- The forcing term for Chebyshev polynomials at two possibly noncommuting matrices. -/
def chebyshevForcing (j : ℕ) : R :=
  if j = 0 then y - x else 2 * (y - x) * matrixChebyshevT y j

def chebyshevResponse : R :=
  ∑ j ∈ Finset.range n, matrixChebyshevU x (n - 1 - j) * f j

theorem chebyshevResponse_recurrence :
    chebyshevResponse x f (n + 2) =
      2 * x * chebyshevResponse x f (n + 1) - chebyshevResponse x f n + f (n + 1) := by
  unfold chebyshevResponse
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  simp only [show (n : ℤ) + 2 - 1 - n = 1 by ring,
    show (n : ℤ) + 2 - 1 - (n + 1) = 0 by ring,
    show (n : ℤ) + 1 - 1 - n = 0 by ring]
  simp only [matrixChebyshevU, Chebyshev.U_zero, Chebyshev.U_one,
    map_one, map_mul, map_ofNat, aeval_X, one_mul]
  change (∑ j ∈ Finset.range n, matrixChebyshevU x (n + 2 - 1 - j) * f j) +
    2 * x * f n + f (n + 1) =
    2 * x * ((∑ j ∈ Finset.range n, matrixChebyshevU x (n + 1 - 1 - j) * f j) + f n) -
      ∑ j ∈ Finset.range n, matrixChebyshevU x (n - 1 - j) * f j + f (n + 1)
  have hindex j : n + 2 - 1 - j = ((n : ℤ) + 1 - 1 - j) + 1 := by ring
  simp_rw [hindex, matrixChebyshevU_recurrence]
  have hindex' j : n + 1 - 1 - j - 1 = (n : ℤ) - 1 - j := by ring
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  noncomm_ring

/-- Exact discrete variation of constants; no commutativity of the two arguments is assumed. -/
theorem matrixChebyshevT_perturbation_identity :
    matrixChebyshevT y n - matrixChebyshevT x n =
      chebyshevResponse x (chebyshevForcing x y) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [matrixChebyshevT, chebyshevResponse]
  | one => simp [matrixChebyshevT, chebyshevResponse, chebyshevForcing, matrixChebyshevU]
  | more n hn hn1 =>
    rw [matrixChebyshevT_recurrence, matrixChebyshevT_recurrence,
      chebyshevResponse_recurrence, ← hn, ← hn1]
    simp [chebyshevForcing]
    noncomm_ring

end ChebyshevPerturbation

/-- A finite positive weighted geometric constant; it is independent of polynomial degree. -/
def perturbationConstant (η : ℝ) : ℝ := ∑' k, (k + 1 : ℕ) * η ^ k

section
variable {u : ℕ → ℝ} {η δ : ℝ} (hη : 0 < η) (hη1 : η < 1)
include hη hη1

theorem perturbationConstant_pos :
    0 < perturbationConstant η := by
  have hs : Summable (fun k => (k + 1 : ℕ) * η ^ k) := by
    simpa using RoughRegime.SeriesBounds.weighted_geometric_summable 1 η hη hη1
  apply hs.tsum_pos (fun k => by positivity) 0
  simp

theorem weighted_convolution_le_constant (n : ℕ) :
    (∑ j ∈ Finset.range n, (n - j : ℕ) * η ^ (n - j)) ≤ perturbationConstant η := by
  have hs : Summable (fun k => (k + 1 : ℕ) * η ^ k) := by
    simpa using RoughRegime.SeriesBounds.weighted_geometric_summable 1 η hη hη1
  rw [← Finset.sum_range_reflect]
  have he j (hj : j ∈ Finset.range n) : n - (n - 1 - j) = j + 1 := by
    have := Finset.mem_range.mp hj
    omega
  calc
    _ = ∑ j ∈ Finset.range n, (j + 1 : ℕ) * η ^ (j + 1) := by
      apply Finset.sum_congr rfl
      simp_all
    _ ≤ _ := by
      bound
    _ ≤ _ := hs.sum_le_tsum _ (fun k hk => by positivity)

/-- Discrete Gronwall majorant with a second-order convolution kernel. -/
theorem recurrence_exponential_majorant (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hu : ∀ n, u n ≤ 1 + 2 * δ *
      ∑ j ∈ Finset.range n, (n - j : ℕ) * u j) (n : ℕ) :
    η ^ n * u n ≤ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hterm j (hj : j ∈ Finset.range n) :
        η ^ n * ((n - j : ℕ) * u j) ≤
          2 * ((n - j : ℕ) * η ^ (n - j)) := by
      have hjn := Finset.mem_range.mp hj
      have hp : η ^ n = η ^ (n - j) * η ^ j := by
        rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hjn)]
      calc
        _ = ((n - j : ℕ) * η ^ (n - j)) * (η ^ j * u j) := by rw [hp]; ring
        _ ≤ ((n - j : ℕ) * η ^ (n - j)) * 2 :=
          by bound
        _ = _ := by ring
    calc
      _ ≤ η ^ n * (1 + 2 * δ * ∑ j ∈ Finset.range n, (n - j : ℕ) * u j) :=
        by bound
      _ = η ^ n + 2 * δ * ∑ j ∈ Finset.range n,
          η ^ n * ((n - j : ℕ) * u j) := by rw [← Finset.mul_sum]; ring
      _ ≤ _ :=
        add_le_add (pow_le_one₀ hη.le hη1.le) (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity))
      _ = _ := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ _ :=
        add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left
          (weighted_convolution_le_constant hη hη1 n) (show 0 ≤ 4 * δ by positivity))
      _ ≤ 2 := by linarith

end

section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]

private theorem norm_two_ring : ‖(2 : R)‖ = 2 := by
  have h : 2 = (2 : ℝ) • (1 : R) := by norm_num [Algebra.smul_def, map_ofNat]
  simp_all

variable {x y : R} (hx : ∀ n, ‖matrixChebyshevT x n‖ ≤ 1) {η δ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hδ : 0 ≤ δ) (hsmall : 4 * δ * perturbationConstant η ≤ 1) (hd : ‖y - x‖ ≤ δ) (n : ℕ)

include hx in
theorem matrixChebyshevU_norm_le :
    ‖matrixChebyshevU x n‖ ≤ n + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [matrixChebyshevU]
  | one =>
    have hx1 : ‖x‖ ≤ 1 := by simpa [matrixChebyshevT] using hx 1
    simp only [matrixChebyshevU, Nat.cast_one, Chebyshev.U_one, map_mul, map_ofNat, aeval_X]
    calc
      _ ≤ _ := norm_mul_le _ _
      _ ≤ 2 := by rw [norm_two_ring]; linarith
      _ = _ := by norm_num
  | more n hn hn1 =>
    have he : matrixChebyshevU x (n + 2 : ℕ) =
        2 * matrixChebyshevT x (n + 2) + matrixChebyshevU x n := by
      unfold matrixChebyshevU matrixChebyshevT
      rw [show (n + 2 : ℕ) = (n : ℤ) + 2 by omega, Chebyshev.U_eq_two_mul_T_add_U]
      simp [map_ofNat]
    rw [he]
    calc
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add (by simpa only [norm_two_ring] using norm_mul_le (2 : R) _) hn
      _ ≤ _ := by have h := hx (n + 2); push_cast; linarith

include hδ hd in
theorem chebyshevForcing_norm_le (j : ℕ) :
    ‖chebyshevForcing x y j‖ ≤ 2 * δ * ‖matrixChebyshevT y j‖ := by
  unfold chebyshevForcing
  split_ifs with hj
  · subst j
    simpa [matrixChebyshevT] using hd.trans (show δ ≤ 2 * δ by linarith)
  · calc
      _ ≤ _ := norm_mul_le _ _
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (norm_mul_le _ _).trans (by rw [norm_two_ring]; gcongr)

include hx hδ hd in
theorem matrixChebyshevT_norm_volterra :
    ‖matrixChebyshevT y n‖ ≤ 1 + 2 * δ *
      ∑ j ∈ Finset.range n, (n - j : ℕ) * ‖matrixChebyshevT y j‖ := by
  have hterm j (hj : j ∈ Finset.range n) :
      ‖matrixChebyshevU x (n - 1 - j) * chebyshevForcing x y j‖ ≤
        2 * δ * ((n - j : ℕ) * ‖matrixChebyshevT y j‖) := by
    have hjn := Finset.mem_range.mp hj
    have hi : n - 1 - j = ((n - 1 - j : ℕ) : ℤ) := by omega
    have hn : (n - 1 - j : ℕ) + 1 = ((n - j : ℕ) : ℝ) := by
      exact_mod_cast (show n - 1 - j + 1 = n - j by omega)
    rw [hi]
    calc
      _ ≤ _ := norm_mul_le _ _
      _ ≤ _ :=
        mul_le_mul (matrixChebyshevU_norm_le hx _) (chebyshevForcing_norm_le hδ hd j)
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [hn]; ring
  have he  := sub_eq_iff_eq_add'.mp (matrixChebyshevT_perturbation_identity x y n)
  rw [he]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ _ :=
      add_le_add (hx n) (norm_sum_le _ _)
    _ ≤ 1 + ∑ j ∈ Finset.range n,
        2 * δ * ((n - j : ℕ) * ‖matrixChebyshevT y j‖) :=
      by bound
    _ = _ := by rw [Finset.mul_sum]

include hx hη hη1 hδ hsmall hd in
/-- Uniform exponential control in a fixed noncommutative neighborhood of a bounded
Chebyshev center. The radius depends on `η`, never on the polynomial degree. -/
theorem matrixChebyshevT_neighborhood_bound :
    η ^ n * ‖matrixChebyshevT y n‖ ≤ 2 :=
  recurrence_exponential_majorant hη hη1 hδ hsmall
    (matrixChebyshevT_norm_volterra hx hδ hd) n

end ChebyshevNorm

section PowerSeriesBounds
variable {R I : Type*} [NormedCommRing R] [NormOneClass R] [DecidableEq I]

/-- Finite Cauchy products preserve a common geometric envelope in any normed
commutative ring, including the complexified matrix entries. -/
theorem powerSeries_prod_geometric_bound (s : Finset I) (f : I → PowerSeries R)
    {q B : ℝ} (hq : 0 < q) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, ∀ k, ‖PowerSeries.coeff k (f i)‖ ≤ B * q ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖ ≤
      B ^ s.card * (k + 1 : ℕ) ^ s.card * q ^ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp
    split_ifs with hk
    · subst k; simp
    · simp; positivity
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    have hh := RoughRegime.SeriesBounds.convolution_coefficient_bound s.card k hq
      (by positivity) hB
      (fun j => ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) j)
      (hf a (Finset.mem_insert_self ..))
    rw [PowerSeries.coeff_mul]
    simpa only [RoughRegime.SeriesBounds.convolution, Finset.card_insert_of_notMem ha,
      pow_succ] using hh

end PowerSeriesBounds

section ComplexMatrices
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

section
variable (lo hi : ℝ) (A B : Matrix n n ℂ)

def normalizeMatrix : Matrix n n ℂ :=
  (intervalHalfWidth lo hi)⁻¹ • (A - intervalCenter lo hi • 1)

theorem normalizedChebyshev_aeval_complex (k : ℕ) :
    aeval A (normalizedChebyshev lo hi k) = matrixChebyshevT (normalizeMatrix lo hi A) k := by
  rw [normalizedChebyshev, aeval_comp]
  congr 1
  simp [normalizeMatrix, Algebra.smul_def]

theorem normalizedChebyshev_complex_center_bound {lo hi : ℝ} (hlo : 0 < lo) (hlt : lo < hi)
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hSpec : spectrum ℝ A ⊆ Set.Icc lo hi) (k : ℕ) :
    ‖matrixChebyshevT (normalizeMatrix lo hi A) k‖ ≤ 1 := by
  rw [← normalizedChebyshev_aeval_complex, ← cfc_polynomial _ A (Matrix.isHermitian_iff_isSelfAdjoint.mp hA)]
  apply norm_cfc_le (by norm_num)
  intro x hx
  rw [normalizedChebyshev_eval, Real.norm_eq_abs]
  grind [RoughRegime.Upper.chebyshev_abs_le_one, interval_argument_mem]

theorem normalizeMatrix_sub :
    normalizeMatrix lo hi B - normalizeMatrix lo hi A =
      (intervalHalfWidth lo hi)⁻¹ • (B - A) := by
  simp only [normalizeMatrix, ← smul_sub]
  abel

end

theorem matrix_entry_norm_le_l2 (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  let T := Matrix.toEuclideanCLM (𝕜 := ℂ) A
  have hi := PiLp.norm_apply_le (T e) i
  have hentry : (T e) i = A i j := by
    simp [T, e, Matrix.toEuclideanCLM_toLp, EuclideanSpace.single, Matrix.mulVec, dotProduct]
  rw [hentry] at hi
  exact hi.trans (by simpa [he, T, Matrix.l2_opNorm_toEuclideanCLM] using
    (T.le_opNorm e))

/-- The complex kernel is evaluated at arbitrary, possibly nonnormal matrices. -/
def complexKernelSeries (lo hi : ℝ) (A : Matrix n n ℂ) : Matrix n n (PowerSeries ℂ) :=
  fun i j => PowerSeries.mk (fun k => (aeval A (kernelCoefficientPolynomial lo hi k)) i j)

theorem complex_kernel_coefficient_bound {lo hi : ℝ} (hlo : 0 < lo) (hlt : lo < hi)
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hSpec : spectrum ℝ A ⊆ Set.Icc lo hi)
    {η δ : ℝ} (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hd : ‖normalizeMatrix lo hi B - normalizeMatrix lo hi A‖ ≤ δ) (k : ℕ) :
    ‖aeval B (kernelCoefficientPolynomial lo hi k)‖ ≤
      4 * (intervalRho lo hi / η) ^ k := by
  have hb := matrixChebyshevT_neighborhood_bound
    (normalizedChebyshev_complex_center_bound hlo hlt (A := A) hA hSpec) hη hη1 hδ hsmall hd k
  unfold kernelCoefficientPolynomial
  rw [map_mul, aeval_C, ← Algebra.smul_def, norm_smul, normalizedChebyshev_aeval_complex]
  have hr := intervalRho_pos lo hi hlo hlt
  split_ifs with hk
  · subst k
    simp [matrixChebyshevT]
  · rw [Real.norm_eq_abs, abs_mul, 
      abs_pow, abs_neg, abs_of_pos hr]
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hη k)).mpr
    calc
      _ = 2 * intervalRho lo hi ^ k * (η ^ k * ‖matrixChebyshevT (normalizeMatrix lo hi B) k‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

section
variable {K L : Matrix n n (PowerSeries ℂ)} {q B : ℝ} (hq : 0 < q) (hq1 : q < 1) (hB : 0 ≤ B)
    (hK : ∀ i j k, ‖PowerSeries.coeff k (K i j)‖ ≤ B * q ^ k)
include hq hB hK

theorem determinant_series_coefficient_bound (k : ℕ) :
    ‖PowerSeries.coeff k K.det‖ ≤
      (Fintype.card (Equiv.Perm n)) * B ^ Fintype.card n *
        (k + 1 : ℕ) ^ Fintype.card n * q ^ k := by
  rw [Matrix.det_apply, map_sum]
  calc
    _ ≤ _ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (∏ i, K (σ i) i)‖ := by
      simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro σ hσ
      exact powerSeries_prod_geometric_bound Finset.univ (fun i => K (σ i) i) hq hB
        (fun i hi => hK _ _ ) k
    _ = _ := by simp [mul_assoc]

include hq1 in
/-- A finite combined-index inverse/determinant truncation admits a common
degree-independent bound whenever its entries share a geometric envelope. -/
theorem combined_truncation_uniform_bound
    (hL : ∀ i j k, ‖PowerSeries.coeff k (L i j)‖ ≤ B * q ^ k)
    (i j : n) (m : ℕ) :
    ‖∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (K i j * L.det)‖ ≤
      ((Fintype.card (Equiv.Perm n)) * B ^ (Fintype.card n + 1)) *
        ∑' k, (k + 1 : ℕ) ^ (Fintype.card n + 1) * q ^ k := by
  let A  := (Fintype.card (Equiv.Perm n)) * B ^ (Fintype.card n + 1)
  have hcoeff k : ‖PowerSeries.coeff k (K i j * L.det)‖ ≤
      A * (k + 1 : ℕ) ^ (Fintype.card n + 1) * q ^ k := by
    rw [mul_comm, PowerSeries.coeff_mul]
    have hh := RoughRegime.SeriesBounds.convolution_coefficient_bound
      (Fintype.card n) k
      hq (by positivity) hB (determinant_series_coefficient_bound hq hB hL) (hK i j)
    simpa [RoughRegime.SeriesBounds.convolution, A, pow_succ, mul_assoc] using hh
  calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1), A * (k + 1 : ℕ) ^ (Fintype.card n + 1) * q ^ k :=
      by bound
    _ ≤ _ := by
      simpa only [mul_assoc] using ((RoughRegime.SeriesBounds.weighted_geometric_summable (Fintype.card n + 1) q hq hq1).mul_left A).sum_le_tsum (Finset.range (m + 1)) (fun k hk => by positivity)
    _ = _ := by rw [tsum_mul_left]

end

section
variable (p : ℝ[X]) (lo hi : ℝ) (A : Matrix n n ℂ)

theorem variableMatrix_power_eval_complex (k : ℕ) (i j : n) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun ij => A ij.1 ij.2)
      ((variableMatrix n ^ k) i j) = (A ^ k) i j := by
  induction k generalizing i j with
  | zero => simp [pow_zero, Matrix.one_apply]; split_ifs <;> simp
  | succ k ih =>
    simp [pow_succ, Matrix.mul_apply, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, ih]
    simp [variableMatrix]

theorem matrixEntryPolynomial_eval_complex (i j : n) :
    MvPolynomial.eval₂ Complex.ofRealHom (fun ij => A ij.1 ij.2)
      (matrixEntryPolynomial p i j) = (aeval A p) i j := by
  rw [Polynomial.aeval_eq_sum_range]
  unfold matrixEntryPolynomial
  simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    variableMatrix_power_eval_complex, Matrix.sum_apply, Matrix.smul_apply]
  rfl

theorem variableKernelSeries_eval_complex :
    (PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (fun ij => A ij.1 ij.2))).mapMatrix
      (variableKernelSeries lo hi) = complexKernelSeries lo hi A := by
  ext i j k
  exact matrixEntryPolynomial_eval_complex _ A i j

end

/-- Complexification of real matrices preserves the real functional calculus. -/
def ofRealMatrixStarAlgHom : Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n ℂ :=
  { Complex.ofRealHom.mapMatrix with
    commutes' := by
      intro a
      ext i j
      change (if i = j then a else 0 : ℝ) = if i = j then (a : ℂ) else 0
      split_ifs <;> simp
    map_star' := by
      intro A
      ext i j
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] }

theorem ofRealMatrixStarAlgHom_injective : Function.Injective (ofRealMatrixStarAlgHom (n := n)) := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective (congrArg (fun M => M i j) h)

theorem complexify_matrix_spectrum {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    spectrum ℝ (A.map Complex.ofReal) = spectrum ℝ A := (Matrix.isHermitian_iff_isSelfAdjoint.mp hA).map_spectrum_real (ofRealMatrixStarAlgHom)
    ofRealMatrixStarAlgHom_injective
    (ofRealMatrixStarAlgHom).toAlgHom.toLinearMap.continuous_of_finiteDimensional

end ComplexMatrices

section ComplexFreeCoordinates
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.CombinedPolynomial RoughRegime.MatrixDeterminant
variable (r : ℕ) [NeZero r]

variable (lo hi : ℝ) (A C : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r)

def complexParentValuation : parentInverseVariables r → ℂ
  | Sum.inl ij => A ij.1 ij.2
  | Sum.inr ⟨_, ij⟩ => C ij.1 ij.2

theorem eval_renamed_series_complex {V W : Type*} (f : V → W) (values : W → ℂ)
    (P : PowerSeries (MvPolynomial V ℝ)) :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom values)
      (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
      PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (values ∘ f)) P := by
  ext k
  exact MvPolynomial.eval₂_rename ..

theorem inverseVariableSeries_eval_complex :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexParentValuation r A C))
      (inverseVariableSeries (fun _ => r) lo hi i j) = complexKernelSeries lo hi A i j := by
  rw [inverseVariableSeries, eval_renamed_series_complex]
  exact congrArg (fun K => K i j) (variableKernelSeries_eval_complex lo hi A)

theorem determinantVariableSeries_eval_complex (t : Fin 1) :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexParentValuation r A C))
      (determinantVariableSeries r (fun _ => r) lo hi t) =
      (complexKernelSeries lo hi C).det := by
  rw [determinantVariableSeries, eval_renamed_series_complex]
  change PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (fun ij => C ij.1 ij.2))
    (variableKernelSeries lo hi).det = _
  rw [RingHom.map_det, variableKernelSeries_eval_complex]

theorem parentInverseEntryPolynomial_eval_complex (m : ℕ) :
    MvPolynomial.eval₂ Complex.ofRealHom (complexParentValuation r A C)
      (parentInverseEntryPolynomial lo hi m i j) =
      ((intervalGeometricMean lo hi ^ (r + 1))⁻¹) *
        ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff k (complexKernelSeries lo hi A i j * (complexKernelSeries lo hi C).det) := by
  have he : PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexParentValuation r A C))
      (combinedVariableSeries _ lo hi i j) =
      complexKernelSeries lo hi A i j * (complexKernelSeries lo hi C).det := by
    simp only [combinedVariableSeries, map_mul, map_prod, inverseVariableSeries_eval_complex,
      determinantVariableSeries_eval_complex, Fin.prod_univ_one]
  simp only [parentInverseEntryPolynomial, truncationEntryPolynomial, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum, combinedCoefficientPolynomial]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hc := congrArg (fun P => PowerSeries.coeff k P) he
  assumption

end ComplexFreeCoordinates

section PolynomialBounds
variable {V : Type*} [Fintype V] [DecidableEq V]

variable (P : MvPolynomial V ℝ) (R : ℝ)

/-- A concrete finite coefficient envelope for a real polynomial on a complex coordinate ball. -/
def polynomialCoordinateBound : ℝ :=
  ∑ α ∈ P.support, ‖P.coeff α‖ * ∏ j, R ^ α j

theorem polynomial_complex_coordinate_bound {z : V → ℂ}
    {R : ℝ} (hR : 0 ≤ R) (hz : ∀ j, ‖z j‖ ≤ R) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z P‖ ≤ polynomialCoordinateBound P R := by
  rw [MvPolynomial.eval₂_eq']
  calc
    _ ≤ _ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro α hα
      rw [norm_mul, norm_prod]
      change ‖(P.coeff α : ℂ)‖ * _ ≤ _
      rw [Complex.norm_real]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun j hj => norm_nonneg _)
      intro j hj
      rw [norm_pow]
      bound

end PolynomialBounds

section CoordinateOperators
open scoped Matrix.Norms.L2Operator
variable (r : ℕ) [NeZero r]

def currentCoordinateMatrix : (incrementVariables r → ℂ) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ where
  toFun z i j := z (Sum.inl (Sum.inl (i, j)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def parentCoordinateMatrix : (incrementVariables r → ℂ) →ₗ[ℂ] Matrix (Fin r) (Fin r) ℂ where
  toFun z i j := z (Sum.inl (Sum.inr ⟨0, (i, j)⟩))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def currentCoordinateCLM : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ :=
  (currentCoordinateMatrix r).toContinuousLinearMap

def parentCoordinateCLM : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ :=
  (parentCoordinateMatrix r).toContinuousLinearMap

theorem coordinate_parent_valuation (z : incrementVariables r → ℂ) :
    z ∘ Sum.inl = complexParentValuation r (currentCoordinateCLM r z) (parentCoordinateCLM r z) := by
  funext v
  cases v with
  | inl ij => rfl
  | inr t =>
    rcases t with ⟨t, ij⟩
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    rfl

open RoughRegime.Upper

end CoordinateOperators

section UniformNeighborhood
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper
variable (r : ℕ) [NeZero r]

end UniformNeighborhood

section ActualDerivatives
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.ComplexDerivativeBridge
variable (r : ℕ) [NeZero r]

variable (u : incrementVariables r → ℝ) (lo hi : ℝ)

/-- The paper's free moment polynomial after the canonical finite coordinate enumeration. -/
def incrementFinPolynomial (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (i : Fin r) :
    MvPolynomial (Fin (Fintype.card (incrementVariables r))) ℝ :=
  MvPolynomial.rename (Fintype.equivFin (incrementVariables r))
    (incrementEntryPolynomial lo hi T y m i)

def currentRealCoordinateMatrix : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => u (Sum.inl (Sum.inl (i, j)))

def parentRealCoordinateMatrix : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => u (Sum.inl (Sum.inr ⟨0, (i, j)⟩))

end ActualDerivatives
end NearlyMinimax
