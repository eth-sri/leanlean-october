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

def matrixChebyshevT (x : R) (n : ℕ) : R := aeval x (Chebyshev.T ℝ (n : ℤ))
def matrixChebyshevU (x : R) (n : ℤ) : R := aeval x (Chebyshev.U ℝ n)

section
variable (x : R)

theorem matrixChebyshevT_recurrence (n : ℕ) :
    matrixChebyshevT x (n + 2) = 2 * x * matrixChebyshevT x (n + 1) - matrixChebyshevT x n := by
  unfold matrixChebyshevT
  rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega, Chebyshev.T_add_two]
  simp [map_ofNat]

theorem matrixChebyshevU_recurrence (n : ℤ) :
    matrixChebyshevU x (n + 1) = 2 * x * matrixChebyshevU x n - matrixChebyshevU x (n - 1) := by
  unfold matrixChebyshevU
  rw [Chebyshev.U_add_one]
  simp [map_ofNat]

end

/-- The forcing term for Chebyshev polynomials at two possibly noncommuting matrices. -/
def chebyshevForcing (x y : R) (j : ℕ) : R :=
  if j = 0 then y - x else 2 * (y - x) * matrixChebyshevT y j

def chebyshevResponse (x : R) (f : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range n, matrixChebyshevU x ((n : ℤ) - 1 - j) * f j

theorem chebyshevResponse_recurrence (x : R) (f : ℕ → R) (n : ℕ) :
    chebyshevResponse x f (n + 2) =
      2 * x * chebyshevResponse x f (n + 1) - chebyshevResponse x f n + f (n + 1) := by
  unfold chebyshevResponse
  push_cast
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  push_cast
  simp only [show (n : ℤ) + 2 - 1 - n = 1 by ring,
    show (n : ℤ) + 2 - 1 - (n + 1) = 0 by ring,
    show (n : ℤ) + 1 - 1 - n = 0 by ring]
  simp only [matrixChebyshevU, Chebyshev.U_zero, Chebyshev.U_one,
    map_one, map_mul, map_ofNat, aeval_X, one_mul]
  change (∑ j ∈ Finset.range n, matrixChebyshevU x ((n : ℤ) + 2 - 1 - j) * f j) +
    2 * x * f n + f (n + 1) =
    2 * x * ((∑ j ∈ Finset.range n, matrixChebyshevU x ((n : ℤ) + 1 - 1 - j) * f j) + f n) -
      ∑ j ∈ Finset.range n, matrixChebyshevU x ((n : ℤ) - 1 - j) * f j + f (n + 1)
  have hindex (j : ℕ) : (n : ℤ) + 2 - 1 - j = ((n : ℤ) + 1 - 1 - j) + 1 := by ring
  simp_rw [hindex, matrixChebyshevU_recurrence]
  have hindex' (j : ℕ) : (n : ℤ) + 1 - 1 - j - 1 = (n : ℤ) - 1 - j := by ring
  simp_rw [hindex']
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  noncomm_ring

/-- Exact discrete variation of constants; no commutativity of the two arguments is assumed. -/
theorem matrixChebyshevT_perturbation_identity (x y : R) (n : ℕ) :
    matrixChebyshevT y n - matrixChebyshevT x n =
      chebyshevResponse x (chebyshevForcing x y) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [matrixChebyshevT, chebyshevResponse]
  | one => simp [matrixChebyshevT, chebyshevResponse, chebyshevForcing, matrixChebyshevU]
  | more n hn hn1 =>
    rw [matrixChebyshevT_recurrence, matrixChebyshevT_recurrence,
      chebyshevResponse_recurrence, ← hn, ← hn1]
    simp only [chebyshevForcing, show n + 1 ≠ 0 by omega, ↓reduceIte]
    noncomm_ring

end ChebyshevPerturbation

/-- A finite positive weighted geometric constant; it is independent of polynomial degree. -/
def perturbationConstant (η : ℝ) : ℝ := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * η ^ k

section
variable (η : ℝ) (hη : 0 < η) (hη1 : η < 1)
include hη hη1

theorem perturbationConstant_pos :
    0 < perturbationConstant η := by
  have hs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * η ^ k) := by
    simpa using RoughRegime.SeriesBounds.weighted_geometric_summable 1 η hη hη1
  unfold perturbationConstant
  apply hs.tsum_pos (fun k => by positivity) 0
  simp

theorem weighted_convolution_le_constant (n : ℕ) :
    (∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * η ^ (n - j)) ≤ perturbationConstant η := by
  have hs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * η ^ k) := by
    simpa using RoughRegime.SeriesBounds.weighted_geometric_summable 1 η hη hη1
  rw [← Finset.sum_range_reflect]
  have he (j : ℕ) (hj : j ∈ Finset.range n) : n - (n - 1 - j) = j + 1 := by
    have := Finset.mem_range.mp hj
    omega
  calc
    _ = ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) * η ^ (j + 1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [he j hj]
    _ ≤ ∑ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) * η ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      rw [pow_succ]
      field_simp <;> linarith
    _ ≤ _ := hs.sum_le_tsum (Finset.range n) (fun k hk => by positivity)

end

/-- Discrete Gronwall majorant with a second-order convolution kernel. -/
theorem recurrence_exponential_majorant (u : ℕ → ℝ) (η δ : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hu : ∀ n, u n ≤ 1 + 2 * δ *
      ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * u j) (n : ℕ) :
    η ^ n * u n ≤ 2 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
        η ^ n * (((n - j : ℕ) : ℝ) * u j) ≤
          2 * (((n - j : ℕ) : ℝ) * η ^ (n - j)) := by
      have hjn := Finset.mem_range.mp hj
      have hp : η ^ n = η ^ (n - j) * η ^ j := by
        rw [← pow_add, Nat.sub_add_cancel (Nat.le_of_lt hjn)]
      calc
        _ = (((n - j : ℕ) : ℝ) * η ^ (n - j)) * (η ^ j * u j) := by rw [hp]; ring
        _ ≤ (((n - j : ℕ) : ℝ) * η ^ (n - j)) * 2 :=
          mul_le_mul_of_nonneg_left (ih j hjn) (by positivity)
        _ = _ := by ring
    have hsum := Finset.sum_le_sum hterm
    have hpow : η ^ n ≤ 1 := pow_le_one₀ hη.le hη1.le
    calc
      η ^ n * u n ≤ η ^ n * (1 + 2 * δ * ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * u j) :=
        mul_le_mul_of_nonneg_left (hu n) (pow_nonneg hη.le n)
      _ = η ^ n + 2 * δ * ∑ j ∈ Finset.range n,
          η ^ n * (((n - j : ℕ) : ℝ) * u j) := by rw [← Finset.mul_sum]; ring
      _ ≤ 1 + 2 * δ * ∑ j ∈ Finset.range n,
          2 * (((n - j : ℕ) : ℝ) * η ^ (n - j)) :=
        add_le_add hpow (mul_le_mul_of_nonneg_left hsum (by positivity))
      _ = 1 + 4 * δ * ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * η ^ (n - j) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ 1 + 4 * δ * perturbationConstant η :=
        add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left
          (weighted_convolution_le_constant η hη hη1 n) (show (0 : ℝ) ≤ 4 * δ by positivity))
      _ ≤ 2 := by linarith

section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]

private theorem norm_two_ring : ‖(2 : R)‖ = 2 := by
  have h : (2 : R) = (2 : ℝ) • (1 : R) := by norm_num [Algebra.smul_def, map_ofNat]
  simp_all

theorem matrixChebyshevU_norm_le (x : R) (hx : ∀ n, ‖matrixChebyshevT x n‖ ≤ 1) (n : ℕ) :
    ‖matrixChebyshevU x (n : ℤ)‖ ≤ (n : ℝ) + 1 := by
  induction n using Nat.twoStepInduction with
  | zero => simp [matrixChebyshevU]
  | one =>
    have hx1 : ‖x‖ ≤ 1 := by simpa [matrixChebyshevT] using hx 1
    simp only [matrixChebyshevU, Nat.cast_one, Chebyshev.U_one, map_mul, map_ofNat, aeval_X]
    calc
      _ ≤ ‖(2 : R)‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ 2 := by simp_all [norm_two_ring]
      _ = _ := by norm_num
  | more n hn hn1 =>
    have he : matrixChebyshevU x ((n + 2 : ℕ) : ℤ) =
        2 * matrixChebyshevT x (n + 2) + matrixChebyshevU x (n : ℤ) := by
      unfold matrixChebyshevU matrixChebyshevT
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by omega, Chebyshev.U_eq_two_mul_T_add_U]
      simp [map_ofNat]
    rw [he]
    calc
      _ ≤ ‖2 * matrixChebyshevT x (n + 2)‖ + ‖matrixChebyshevU x (n : ℤ)‖ := norm_add_le _ _
      _ ≤ 2 * ‖matrixChebyshevT x (n + 2)‖ + ((n : ℝ) + 1) := add_le_add (by simpa only [norm_two_ring] using norm_mul_le (2 : R) _) hn
      _ ≤ _ := by have h := hx (n + 2); push_cast; linarith

section
variable (x y : R)

theorem chebyshevForcing_norm_le (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ‖y - x‖ ≤ δ) (j : ℕ) :
    ‖chebyshevForcing x y j‖ ≤ 2 * δ * ‖matrixChebyshevT y j‖ := by
  unfold chebyshevForcing
  split_ifs with hj
  · subst j
    simpa [matrixChebyshevT] using hd.trans (show δ ≤ 2 * δ by linarith)
  · calc
      _ ≤ ‖(2 : R) * (y - x)‖ * ‖matrixChebyshevT y j‖ := norm_mul_le _ _
      _ ≤ (2 * δ) * ‖matrixChebyshevT y j‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact (norm_mul_le _ _).trans (by simp_all [norm_two_ring])

section
variable (hx : ∀ n, ‖matrixChebyshevT x n‖ ≤ 1)
include hx

theorem matrixChebyshevT_norm_volterra (δ : ℝ) (hδ : 0 ≤ δ)
    (hd : ‖y - x‖ ≤ δ) (n : ℕ) :
    ‖matrixChebyshevT y n‖ ≤ 1 + 2 * δ *
      ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖ := by
  have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
      ‖matrixChebyshevU x ((n : ℤ) - 1 - j) * chebyshevForcing x y j‖ ≤
        2 * δ * (((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖) := by
    have hjn := Finset.mem_range.mp hj
    have hi : (n : ℤ) - 1 - j = ((n - 1 - j : ℕ) : ℤ) := by omega
    have hn : ((n - 1 - j : ℕ) : ℝ) + 1 = ((n - j : ℕ) : ℝ) := by
      exact_mod_cast (show n - 1 - j + 1 = n - j by omega)
    rw [hi]
    calc
      _ ≤ ‖matrixChebyshevU x ((n - 1 - j : ℕ) : ℤ)‖ *
          ‖chebyshevForcing x y j‖ := norm_mul_le _ _
      _ ≤ (((n - 1 - j : ℕ) : ℝ) + 1) *
          (2 * δ * ‖matrixChebyshevT y j‖) :=
        mul_le_mul (matrixChebyshevU_norm_le x hx _) (chebyshevForcing_norm_le x y δ hδ hd j)
          (norm_nonneg _) (by positivity)
      _ = _ := by rw [hn]; ring
  have he : matrixChebyshevT y n = matrixChebyshevT x n +
      chebyshevResponse x (chebyshevForcing x y) n := by
    have h := matrixChebyshevT_perturbation_identity x y n
    exact sub_eq_iff_eq_add'.mp h
  rw [he]
  calc
    _ ≤ ‖matrixChebyshevT x n‖ + ‖chebyshevResponse x (chebyshevForcing x y) n‖ := norm_add_le _ _
    _ ≤ 1 + ∑ j ∈ Finset.range n,
        ‖matrixChebyshevU x ((n : ℤ) - 1 - j) * chebyshevForcing x y j‖ :=
      add_le_add (hx n) (norm_sum_le _ _)
    _ ≤ 1 + ∑ j ∈ Finset.range n,
        2 * δ * (((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖) :=
      add_le_add (le_refl 1) (Finset.sum_le_sum hterm)
    _ = _ := by rw [Finset.mul_sum]

/-- Uniform exponential control in a fixed noncommutative neighborhood of a bounded
Chebyshev center. The radius depends on `η`, never on the polynomial degree. -/
theorem matrixChebyshevT_neighborhood_bound (η δ : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1) (hd : ‖y - x‖ ≤ δ) (n : ℕ) :
    η ^ n * ‖matrixChebyshevT y n‖ ≤ 2 :=
  recurrence_exponential_majorant (fun n => ‖matrixChebyshevT y n‖) η δ hη hη1 hδ hsmall
    (matrixChebyshevT_norm_volterra x y hx δ hδ hd) n

end

end

end ChebyshevNorm

section ComplexMatrices
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.MatrixUpper RoughRegime.MatrixDeterminant
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def normalizeMatrix (lo hi : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (intervalHalfWidth lo hi)⁻¹ • (A - intervalCenter lo hi • 1)

section
variable (lo hi : ℝ)

theorem normalizedChebyshev_aeval_complex (A : Matrix n n ℂ) (k : ℕ) :
    aeval A (normalizedChebyshev lo hi k) = matrixChebyshevT (normalizeMatrix lo hi A) k := by
  rw [normalizedChebyshev, aeval_comp]
  congr 1
  simp [normalizeMatrix, Algebra.smul_def]

theorem normalizedChebyshev_complex_center_bound (hlo : 0 < lo) (hlt : lo < hi)
    (A : Matrix n n ℂ) (hA : A.IsHermitian) (hSpec : spectrum ℝ A ⊆ Set.Icc lo hi) (k : ℕ) :
    ‖matrixChebyshevT (normalizeMatrix lo hi A) k‖ ≤ 1 := by
  rw [← normalizedChebyshev_aeval_complex]
  exact normalizedChebyshev_aeval_norm_le_one lo hi hlo hlt A (Matrix.isHermitian_iff_isSelfAdjoint.mp hA) hSpec k

theorem normalizeMatrix_sub (A B : Matrix n n ℂ) :
    normalizeMatrix lo hi B - normalizeMatrix lo hi A =
      (intervalHalfWidth lo hi)⁻¹ • (B - A) := by
  simp only [normalizeMatrix, ← smul_sub]
  simp

end

theorem matrix_entry_norm_le_l2 {K : Type*} [RCLike K] (A : Matrix n n K)
    (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace K n := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := K) A
  have hi := PiLp.norm_apply_le (T e) i
  have hentry : (T e) i = A i j := by
    simp [T, e, EuclideanSpace.single, Matrix.mulVec, dotProduct]
  rw [hentry] at hi
  exact hi.trans (by simpa [he, T, Matrix.l2_opNorm_toEuclideanCLM] using
    (T.le_opNorm e))

theorem complex_kernel_coefficient_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hSpec : spectrum ℝ A ⊆ Set.Icc lo hi)
    (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hd : ‖normalizeMatrix lo hi B - normalizeMatrix lo hi A‖ ≤ δ) (k : ℕ) :
    ‖aeval B (kernelCoefficientPolynomial lo hi k)‖ ≤
      4 * (intervalRho lo hi / η) ^ k := by
  have hb := matrixChebyshevT_neighborhood_bound
    (normalizeMatrix lo hi A) (normalizeMatrix lo hi B)
    (normalizedChebyshev_complex_center_bound lo hi hlo hlt A hA hSpec)
    η δ hη hη1 hδ hsmall hd k
  unfold kernelCoefficientPolynomial
  rw [map_mul, aeval_C, ← Algebra.smul_def, norm_smul, normalizedChebyshev_aeval_complex]
  have hηk := pow_pos hη k
  have hr := intervalRho_pos lo hi hlo hlt
  split_ifs with hk
  · subst k
    simp [matrixChebyshevT]
  · rw [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 by norm_num,
      abs_pow, abs_neg, abs_of_pos hr]
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ hηk).mpr
    field_simp <;> linarith

theorem determinant_series_coefficient_bound (K : Matrix n n (PowerSeries ℂ))
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hK : ∀ i j k, ‖PowerSeries.coeff k (K i j)‖ ≤ B * q ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k K.det‖ ≤
      (Fintype.card (Equiv.Perm n) : ℝ) * B ^ Fintype.card n *
        ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * q ^ k := by
  have hsign (σ : Equiv.Perm n) (P : PowerSeries ℂ) :
      ‖PowerSeries.coeff k (Equiv.Perm.sign σ • P)‖ = ‖PowerSeries.coeff k P‖ := by
    simp
  rw [Matrix.det_apply, map_sum]
  calc
    _ ≤ ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (Equiv.Perm.sign σ • ∏ i, K (σ i) i)‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (∏ i, K (σ i) i)‖ := by
      solve_by_elim [Finset.sum_congr, hsign]
    _ ≤ ∑ _σ : Equiv.Perm n,
        B ^ Fintype.card n * ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * q ^ k := by
      apply Finset.sum_le_sum
      intro σ hσ
      simpa using RoughRegime.SeriesBounds.coeff_finsetProd_geometric_bound Finset.univ (fun i => K (σ i) i) q B hq hB
        (fun i hi => hK _ _ ) k
    _ = _ := by simp [mul_assoc]

/-- A finite combined-index inverse/determinant truncation admits a common
degree-independent bound whenever its entries share a geometric envelope. -/
theorem combined_truncation_uniform_bound (K L : Matrix n n (PowerSeries ℂ))
    (q B : ℝ) (hq : 0 < q) (hq1 : q < 1) (hB : 0 ≤ B)
    (hK : ∀ i j k, ‖PowerSeries.coeff k (K i j)‖ ≤ B * q ^ k)
    (hL : ∀ i j k, ‖PowerSeries.coeff k (L i j)‖ ≤ B * q ^ k)
    (i j : n) (m : ℕ) :
    ‖∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (K i j * L.det)‖ ≤
      ((Fintype.card (Equiv.Perm n) : ℝ) * B ^ (Fintype.card n + 1)) *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k := by
  let A := (Fintype.card (Equiv.Perm n) : ℝ) * B ^ (Fintype.card n + 1)
  have hcoeff (k : ℕ) : ‖PowerSeries.coeff k (K i j * L.det)‖ ≤
      A * ((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k := by
    rw [mul_comm]
    have hh := RoughRegime.SeriesBounds.coeff_mul_geometric_bound L.det (K i j)
      (Fintype.card n) k q ((Fintype.card (Equiv.Perm n) : ℝ) * B ^ Fintype.card n) B
      hq (by positivity) hB (determinant_series_coefficient_bound L q B hq hB hL) (hK i j)
    simpa [A, pow_succ, mul_assoc] using hh
  have hs := (RoughRegime.SeriesBounds.weighted_geometric_summable (Fintype.card n + 1) q hq hq1).mul_left A
  calc
    _ ≤ ∑ k ∈ Finset.range (m + 1), ‖PowerSeries.coeff k (K i j * L.det)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1), A * ((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k :=
      Finset.sum_le_sum (fun k hk => hcoeff k)
    _ ≤ ∑' k : ℕ, A * (((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k) := by
      simpa only [mul_assoc] using hs.sum_le_tsum (Finset.range (m + 1)) (fun k hk => by positivity)
    _ = _ := by rw [tsum_mul_left]

/-- Complexification of real matrices preserves the real functional calculus. -/
def ofRealMatrixStarAlgHom : Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n ℂ :=
  { Complex.ofRealHom.mapMatrix with
    commutes' := by
      simp
    map_star' := by
      intro A
      ext i j
      simp }

theorem ofRealMatrixStarAlgHom_injective : Function.Injective (ofRealMatrixStarAlgHom (n := n)) := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective (congrArg (fun M : Matrix n n ℂ => M i j) h)

theorem complexify_matrix_spectrum (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    spectrum ℝ (A.map Complex.ofReal) = spectrum ℝ A := by
  have hs := Matrix.isHermitian_iff_isSelfAdjoint.mp hA
  exact hs.map_spectrum_real (ofRealMatrixStarAlgHom (n := n))
    ofRealMatrixStarAlgHom_injective
    (ofRealMatrixStarAlgHom (n := n)).toAlgHom.toLinearMap.continuous_of_finiteDimensional

end ComplexMatrices

section ComplexFreeCoordinates
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.CombinedPolynomial RoughRegime.MatrixDeterminant
variable (r : ℕ) [NeZero r]

section
variable (lo hi : ℝ) (A C : Matrix (Fin r) (Fin r) ℂ)

theorem parentInverseEntryPolynomial_eval_complex (i j : Fin r) (m : ℕ) :
    MvPolynomial.eval₂ Complex.ofRealHom (entryValuation A (fun _ : Fin 1 => C))
      (parentInverseEntryPolynomial lo hi r m i j) =
      ((intervalGeometricMean lo hi ^ (r + 1))⁻¹ : ℝ) *
        ∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (kernelSeries lo hi A i j * (kernelSeries lo hi C).det) := by
  simpa only [parentInverseEntryPolynomial, Fin.sum_univ_one, Fin.prod_univ_one] using!
    truncationEntryPolynomial_eval r (fun _ : Fin 1 => r) lo hi A (fun _ => C) i j m

end

end ComplexFreeCoordinates

section PolynomialBounds
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A concrete finite coefficient envelope for a real polynomial on a complex coordinate ball. -/
def polynomialCoordinateBound (P : MvPolynomial V ℝ) (R : ℝ) : ℝ :=
  ∑ α ∈ P.support, ‖P.coeff α‖ * ∏ j : V, R ^ α j

section
variable (P : MvPolynomial V ℝ)

theorem polynomialCoordinateBound_nonneg (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ polynomialCoordinateBound P R := by
  unfold polynomialCoordinateBound
  positivity

theorem polynomial_complex_coordinate_bound (z : V → ℂ)
    (R : ℝ) (hz : ∀ j, ‖z j‖ ≤ R) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z P‖ ≤ polynomialCoordinateBound P R := by
  rw [MvPolynomial.eval₂_eq']
  calc
    _ ≤ ∑ α ∈ P.support, ‖Complex.ofRealHom (P.coeff α) * ∏ j : V, z j ^ α j‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro α hα
      rw [norm_mul, norm_prod]
      change ‖(P.coeff α : ℂ)‖ * ∏ j : V, ‖z j ^ α j‖ ≤ _
      rw [Complex.norm_real]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Finset.prod_le_prod₀ (fun j hj => norm_nonneg _)
      intro j hj
      simpa using pow_le_pow_left₀ (norm_nonneg _) (hz j) _

end

end PolynomialBounds

section CoordinateOperators
open scoped Matrix.Norms.L2Operator
variable (r : ℕ)

/-- The current and parent matrix blocks of the free moment vector. -/
def incrementCoordinateMatrix {K : Type*} (parent : Bool) (z : incrementVariables r → K) :
    Matrix (Fin r) (Fin r) K :=
  if parent then fun i j => z (Sum.inl (Sum.inr ⟨0, (i, j)⟩))
  else fun i j => z (Sum.inl (Sum.inl (i, j)))

def incrementCoordinateCLM (parent : Bool) :
    (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := incrementCoordinateMatrix r parent
      map_add' := by cases parent <;> intros <;> rfl
      map_smul' := by cases parent <;> intros <;> rfl }

theorem coordinate_parent_valuation (z : incrementVariables r → ℂ) :
    z ∘ Sum.inl = RoughRegime.CombinedPolynomial.entryValuation (incrementCoordinateCLM r false z)
      (fun _ : Fin 1 => incrementCoordinateCLM r true z) := by
  funext v
  rcases v with ij | ⟨t, ij⟩
  · rfl
  · fin_cases t; rfl

/-- The paper's free moment polynomial after the canonical finite coordinate enumeration. -/
def incrementFinPolynomial (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (i : Fin r) :
    MvPolynomial (Fin (Fintype.card (incrementVariables r))) ℝ :=
  MvPolynomial.rename (Fintype.equivFin (incrementVariables r))
    (incrementEntryPolynomial r lo hi T y m i)

end CoordinateOperators
end NearlyMinimax
