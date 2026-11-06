module
public import NearlyMinimax.PaperIncrement
public import RoughRegime.ComplexDerivativeBridge
public import NearlyMinimax.AnchoredGeometry
@[expose] public section
noncomputable section
section
open Polynomial RoughRegime.Upper RoughRegime.MatrixDeterminant
open scoped BigOperators Matrix.Norms.L2Operator
namespace NearlyMinimax
variable {V W : Type*}
section ChebyshevPerturbation
variable {R : Type*} [Ring R] [Algebra ℝ R]
def matrixChebyshevT (x : R) (n : ℕ) : R := aeval x (Chebyshev.T ℝ ↑n)
def matrixChebyshevU (x : R) (n : ℤ) : R := aeval x (Chebyshev.U ℝ n)
theorem matrixChebyshevT_recurrence (x : R) (n : ℕ) :
    matrixChebyshevT x (n + 2) = 2 * x * matrixChebyshevT x (n + 1) - matrixChebyshevT x n := by
  unfold matrixChebyshevT
  rw [show ((n + 2 : ℕ) : ℤ) = ↑n + 2 by omega, Chebyshev.T_add_two]
  simp [map_ofNat]
theorem matrixChebyshevU_recurrence (x : R) (n : ℤ) :
    matrixChebyshevU x (n + 1) = 2 * x * matrixChebyshevU x n - matrixChebyshevU x (n - 1) := by
  unfold matrixChebyshevU
  rw [Chebyshev.U_add_one]
  simp [map_ofNat]
def chebyshevForcing (x y : R) (j : ℕ) : R :=
  if j = 0 then y - x else 2 * (y - x) * matrixChebyshevT y j
def chebyshevResponse (x : R) (f : ℕ → R) (n : ℕ) : R :=
  ∑ j ∈ Finset.range n, matrixChebyshevU x (↑n - 1 - j) * f j
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
  change (∑ j ∈ Finset.range n, matrixChebyshevU x (↑n + 2 - 1 - j) * f j) +
    2 * x * f n + f (n + 1) =
    2 * x * ((∑ j ∈ Finset.range n, matrixChebyshevU x (↑n + 1 - 1 - j) * f j) + f n) -
      ∑ j ∈ Finset.range n, matrixChebyshevU x (↑n - 1 - j) * f j + f (n + 1)
  have hindex (j : ℕ) : (n : ℤ) + 2 - 1 - j = (n : ℤ) + 1 - 1 - j + 1 := by ring
  simp_rw [hindex, matrixChebyshevU_recurrence]
  have hindex' (j : ℕ) : (n : ℤ) + 1 - 1 - j - 1 = (n : ℤ) - 1 - j := by ring
  simp_rw [hindex']
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  noncomm_ring
end ChebyshevPerturbation
def perturbationConstant (η : ℝ) : ℝ := ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * η ^ k
theorem perturbationConstant_pos (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    0 < perturbationConstant η := by
  have hs : Summable (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * η ^ k) := by
    simpa using RoughRegime.SeriesBounds.weighted_geometric_summable 1 η hη hη1
  apply hs.tsum_pos (fun k => by positivity) 0
  simp
theorem weighted_convolution_le_constant (η : ℝ) (hη : 0 < η) (hη1 : η < 1) (n : ℕ) :
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
      calc
        _ = ((j + 1 : ℕ) : ℝ) * η ^ j * η := by ring
        _ ≤ ((j + 1 : ℕ) : ℝ) * η ^ j * 1 :=
          mul_le_mul_of_nonneg_left hη1.le (by positivity)
        _ = _ := by ring
    _ ≤ _ := hs.sum_le_tsum (Finset.range n) (fun k hk => by positivity)
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
    calc
      η ^ n * u n ≤ η ^ n * (1 + 2 * δ * ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * u j) :=
        mul_le_mul_of_nonneg_left (hu n) (pow_nonneg hη.le n)
      _ = η ^ n + 2 * δ * ∑ j ∈ Finset.range n,
          η ^ n * (((n - j : ℕ) : ℝ) * u j) := by rw [← Finset.mul_sum]; ring
      _ ≤ 1 + 2 * δ * ∑ j ∈ Finset.range n,
          2 * (((n - j : ℕ) : ℝ) * η ^ (n - j)) :=
        add_le_add (pow_le_one₀ hη.le hη1.le) (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity))
      _ = 1 + 4 * δ * ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * η ^ (n - j) := by
        rw [← Finset.mul_sum]
        ring
      _ ≤ 1 + 4 * δ * perturbationConstant η :=
        add_le_add (le_refl 1) (mul_le_mul_of_nonneg_left
          (weighted_convolution_le_constant η hη hη1 n) (show ↑0 ≤ 4 * δ by positivity))
      _ ≤ 2 := by linarith
section ChebyshevNorm
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [NormOneClass R]
theorem matrixChebyshevT_neighborhood_bound (x y : R)
    (hx : ∀ n, ‖matrixChebyshevT x n‖ ≤ 1) (η δ : ℝ)
    (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1) (hd : ‖y - x‖ ≤ δ) (n : ℕ) :
    η ^ n * ‖matrixChebyshevT y n‖ ≤ 2 :=
  have h_matrixChebyshevT_norm_volterra (n : ℕ) : ‖matrixChebyshevT y n‖ ≤ 1 + 2 * δ *
      ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖ := by
    have h_norm_two_ring : ‖(2 : R)‖ = 2 := by
      have h : (2 : R) = (2 : ℝ) • (1 : R) := by norm_num [Algebra.smul_def, map_ofNat]
      rw [h, norm_smul, norm_one, Real.norm_two, mul_one]
    have hterm (j : ℕ) (hj : j ∈ Finset.range n) :
        ‖matrixChebyshevU x ((n : ℤ) - 1 - j) * chebyshevForcing x y j‖ ≤
          2 * δ * (((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖) := by
      have := Finset.mem_range.mp hj
      have hi : (n : ℤ) - 1 - j = ((n - 1 - j : ℕ) : ℤ) := by omega
      have hn : ((n - 1 - j : ℕ) : ℝ) + 1 = ((n - j : ℕ) : ℝ) := by
        exact_mod_cast (show n - 1 - j + 1 = n - j by omega)
      rw [hi]
      have h_chebyshevForcing_norm_le : ‖chebyshevForcing x y j‖ ≤ 2 * δ * ‖matrixChebyshevT y j‖ := by
        unfold chebyshevForcing
        split_ifs with hj
        · subst j
          simpa [matrixChebyshevT] using hd.trans (show δ ≤ 2 * δ by linarith)
        · calc
            _ ≤ ‖(2 : R) * (y - x)‖ * ‖matrixChebyshevT y j‖ := norm_mul_le _ _
            _ ≤ 2 * δ * ‖matrixChebyshevT y j‖ := by
              apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
              exact (norm_mul_le _ _).trans (by rw [h_norm_two_ring]; gcongr)
      have h_matrixChebyshevU_norm_le (n : ℕ) : ‖matrixChebyshevU x (n : ℤ)‖ ≤ (n : ℝ) + 1 := by
        induction n using Nat.twoStepInduction with
        | zero => simp [matrixChebyshevU]
        | one =>
          have : ‖x‖ ≤ 1 := by simpa [matrixChebyshevT] using hx 1
          simp only [matrixChebyshevU, Nat.cast_one, Chebyshev.U_one, map_mul, map_ofNat, aeval_X]
          calc
            _ ≤ ‖(2 : R)‖ * ‖x‖ := norm_mul_le _ _
            _ ≤ 2 := by rw [h_norm_two_ring]; linarith
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
            _ ≤ 2 * ‖matrixChebyshevT x (n + 2)‖ + ((n : ℝ) + 1) := by
              exact add_le_add (by simpa only [h_norm_two_ring] using norm_mul_le (2 : R) _) hn
            _ ≤ _ := by have := hx (n + 2); push_cast; linarith
      calc
        _ ≤ ‖matrixChebyshevU x ((n - 1 - j : ℕ) : ℤ)‖ *
            ‖chebyshevForcing x y j‖ := norm_mul_le _ _
        _ ≤ (((n - 1 - j : ℕ) : ℝ) + 1) *
            (2 * δ * ‖matrixChebyshevT y j‖) :=
          mul_le_mul (h_matrixChebyshevU_norm_le _) h_chebyshevForcing_norm_le
            (norm_nonneg _) (by positivity)
        _ = _ := by rw [hn]; ring
    have h_matrixChebyshevT_perturbation_identity (n : ℕ) : matrixChebyshevT y n - matrixChebyshevT x n =
        chebyshevResponse x (chebyshevForcing x y) n := by
      induction n using Nat.twoStepInduction with
      | zero => simp [matrixChebyshevT, chebyshevResponse]
      | one => simp [matrixChebyshevT, chebyshevResponse, chebyshevForcing, matrixChebyshevU]
      | more n hn hn1 =>
        rw [matrixChebyshevT_recurrence, matrixChebyshevT_recurrence,
          chebyshevResponse_recurrence, ← hn, ← hn1]
        simp only [chebyshevForcing, show n + 1 ≠ 0 by omega, ↓reduceIte]
        noncomm_ring
    rw [sub_eq_iff_eq_add'.mp (h_matrixChebyshevT_perturbation_identity n)]
    calc
      _ ≤ ‖matrixChebyshevT x n‖ + ‖chebyshevResponse x (chebyshevForcing x y) n‖ := norm_add_le _ _
      _ ≤ 1 + ∑ j ∈ Finset.range n,
          ‖matrixChebyshevU x (↑n - 1 - j) * chebyshevForcing x y j‖ :=
        add_le_add (hx n) (norm_sum_le _ _)
      _ ≤ 1 + ∑ j ∈ Finset.range n,
          2 * δ * (((n - j : ℕ) : ℝ) * ‖matrixChebyshevT y j‖) :=
        add_le_add (le_refl 1) (Finset.sum_le_sum hterm)
      _ = _ := by rw [Finset.mul_sum]
  recurrence_exponential_majorant (fun n => ‖matrixChebyshevT y n‖) η δ hη hη1 hδ hsmall
    h_matrixChebyshevT_norm_volterra n
end ChebyshevNorm
section PowerSeriesBounds
variable {R I : Type*} [NormedCommRing R] [NormOneClass R] [DecidableEq I]
theorem powerSeries_prod_geometric_bound (s : Finset I) (f : I → PowerSeries R)
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hf : ∀ i ∈ s, ∀ k, ‖PowerSeries.coeff k (f i)‖ ≤ B * q ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k (∏ i ∈ s, f i)‖ ≤
      B ^ s.card * ((k + 1 : ℕ) : ℝ) ^ s.card * q ^ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    simp only [Finset.prod_empty, Finset.card_empty, pow_zero, one_mul, PowerSeries.coeff_one]
    split_ifs with hk
    · subst k; simp
    · simp only [norm_zero]; positivity
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, mul_comm]
    have hh := RoughRegime.SeriesBounds.convolution_coefficient_bound
      (fun j => PowerSeries.coeff j (∏ i ∈ s, f i))
      (fun j => PowerSeries.coeff j (f a)) s.card k q (B ^ s.card) B hq
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
def normalizeMatrix (lo hi : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  (intervalHalfWidth lo hi)⁻¹ • (A - intervalCenter lo hi • 1)
theorem normalizedChebyshev_aeval_complex (lo hi : ℝ) (A : Matrix n n ℂ) (k : ℕ) :
    aeval A (normalizedChebyshev lo hi k) = matrixChebyshevT (normalizeMatrix lo hi A) k := by
  rw [normalizedChebyshev, aeval_comp]
  congr 1
  simp [normalizeMatrix, Algebra.smul_def]
theorem normalizeMatrix_sub (lo hi : ℝ) (A B : Matrix n n ℂ) :
    normalizeMatrix lo hi B - normalizeMatrix lo hi A =
      (intervalHalfWidth lo hi)⁻¹ • (B - A) := by
  simp only [normalizeMatrix, ← smul_sub]
  congr 1
  abel
theorem matrix_entry_norm_le_l2 (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  let e : EuclideanSpace ℂ n := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  let T := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A
  have hi := PiLp.norm_apply_le (T e) i
  have hentry : (T e) i = A i j := by
    simp [T, e, EuclideanSpace.single, Matrix.mulVec, dotProduct]
  rw [hentry] at hi
  exact hi.trans (by simpa [he, T, Matrix.l2_opNorm_toEuclideanCLM] using
    (T.le_opNorm e))
def complexKernelSeries (lo hi : ℝ) (A : Matrix n n ℂ) : Matrix n n (PowerSeries ℂ) :=
  fun i j => PowerSeries.mk (fun k => (aeval A (kernelCoefficientPolynomial lo hi k)) i j)
theorem complex_kernel_coefficient_bound (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (A B : Matrix n n ℂ) (hA : A.IsHermitian) (hSpec : spectrum ℝ A ⊆ Set.Icc lo hi)
    (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hd : ‖normalizeMatrix lo hi B - normalizeMatrix lo hi A‖ ≤ δ) (k : ℕ) :
    ‖aeval B (kernelCoefficientPolynomial lo hi k)‖ ≤
      4 * (intervalRho lo hi / η) ^ k := by
  have h_normalizedChebyshev_complex_center_bound (k : ℕ) : ‖matrixChebyshevT (normalizeMatrix lo hi A) k‖ ≤ 1 := by
    rw [← normalizedChebyshev_aeval_complex, ← cfc_polynomial _ A (Matrix.isHermitian_iff_isSelfAdjoint.mp hA)]
    apply norm_cfc_le (by norm_num)
    intro x hx
    rw [normalizedChebyshev_eval, Real.norm_eq_abs]
    exact RoughRegime.Upper.chebyshev_abs_le_one _
      (interval_argument_mem lo hi x hlo hlt (hSpec hx)) k
  have hb := matrixChebyshevT_neighborhood_bound
    (normalizeMatrix lo hi A) (normalizeMatrix lo hi B)
    h_normalizedChebyshev_complex_center_bound
    η δ hη hη1 hδ hsmall hd k
  unfold kernelCoefficientPolynomial
  rw [map_mul, aeval_C, ← Algebra.smul_def, norm_smul, normalizedChebyshev_aeval_complex]
  have hηk  := pow_pos hη k
  have hr := intervalRho_pos lo hi hlo hlt
  split_ifs with hk
  · subst k
    simp [matrixChebyshevT]
  · rw [Real.norm_eq_abs, abs_mul, show |(2 : ℝ)| = 2 by norm_num,
      abs_pow, abs_neg, abs_of_pos hr]
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ hηk).mpr
    calc
      _ = 2 * intervalRho lo hi ^ k * (η ^ k * ‖matrixChebyshevT (normalizeMatrix lo hi B) k‖) := by ring
      _ ≤ 2 * intervalRho lo hi ^ k * 2 := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
theorem determinant_series_coefficient_bound (K : Matrix n n (PowerSeries ℂ))
    (q B : ℝ) (hq : 0 < q) (hB : 0 ≤ B)
    (hK : ∀ i j k, ‖PowerSeries.coeff k (K i j)‖ ≤ B * q ^ k) (k : ℕ) :
    ‖PowerSeries.coeff k K.det‖ ≤
      (Fintype.card (Equiv.Perm n) : ℝ) * B ^ Fintype.card n *
        ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * q ^ k := by
  have hsign (σ : Equiv.Perm n) (P : PowerSeries ℂ) :
      ‖PowerSeries.coeff k (Equiv.Perm.sign σ • P)‖ = ‖PowerSeries.coeff k P‖ := by
    obtain hs | hs := Int.units_eq_one_or (Equiv.Perm.sign σ)
    · rw [hs]; simp
    · rw [hs]; simp [Units.smul_def]
  rw [Matrix.det_apply, map_sum]
  calc
    _ ≤ ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (Equiv.Perm.sign σ • ∏ i, K (σ i) i)‖ :=
      norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm n, ‖PowerSeries.coeff k (∏ i, K (σ i) i)‖ := by
      apply Finset.sum_congr rfl; intro σ hσ; exact hsign σ _
    _ ≤ ∑ _σ : Equiv.Perm n,
        B ^ Fintype.card n * ((k + 1 : ℕ) : ℝ) ^ Fintype.card n * q ^ k := by
      apply Finset.sum_le_sum
      intro σ hσ
      simpa using powerSeries_prod_geometric_bound Finset.univ (fun i => K (σ i) i) q B hq hB
        (fun i hi => hK _ _ ) k
    _ = _ := by simp [mul_assoc]
theorem combined_truncation_uniform_bound (K L : Matrix n n (PowerSeries ℂ))
    (q B : ℝ) (hq : 0 < q) (hq1 : q < 1) (hB : 0 ≤ B)
    (hK : ∀ i j k, ‖PowerSeries.coeff k (K i j)‖ ≤ B * q ^ k)
    (hL : ∀ i j k, ‖PowerSeries.coeff k (L i j)‖ ≤ B * q ^ k)
    (i j : n) (m : ℕ) :
    ‖∑ k ∈ Finset.range (m + 1), PowerSeries.coeff k (K i j * L.det)‖ ≤
      (Fintype.card (Equiv.Perm n) : ℝ) * B ^ (Fintype.card n + 1) *
        ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k := by
  let A : ℝ := (Fintype.card (Equiv.Perm n) : ℝ) * B ^ (Fintype.card n + 1)
  have hcoeff (k : ℕ) : ‖PowerSeries.coeff k (K i j * L.det)‖ ≤
      A * ((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k := by
    rw [mul_comm, PowerSeries.coeff_mul]
    have hh := RoughRegime.SeriesBounds.convolution_coefficient_bound
      (fun k => PowerSeries.coeff k L.det) (fun k => PowerSeries.coeff k (K i j))
      (Fintype.card n) k q ((Fintype.card (Equiv.Perm n) : ℝ) * B ^ Fintype.card n) B
      hq (by positivity) hB (determinant_series_coefficient_bound L q B hq hB hL) (hK i j)
    simpa [RoughRegime.SeriesBounds.convolution, A, pow_succ, mul_assoc] using hh
  calc
    _ ≤ ∑ k ∈ Finset.range (m + 1), ‖PowerSeries.coeff k (K i j * L.det)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (m + 1), A * ((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k :=
      Finset.sum_le_sum (fun k hk => hcoeff k)
    _ ≤ ∑' k : ℕ, A * (((k + 1 : ℕ) : ℝ) ^ (Fintype.card n + 1) * q ^ k) := by
      simpa only [mul_assoc] using ((RoughRegime.SeriesBounds.weighted_geometric_summable (Fintype.card n + 1) q hq hq1).mul_left A).sum_le_tsum (Finset.range (m + 1)) (fun k hk => by positivity)
    _ = _ := by rw [tsum_mul_left]
theorem variableKernelSeries_eval_complex (lo hi : ℝ) (A : Matrix n n ℂ) :
    (PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (fun ij : n × n => A ij.1 ij.2))).mapMatrix
      (variableKernelSeries lo hi (n := n)) = complexKernelSeries lo hi A := by
  ext i j k
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, PowerSeries.coeff_map]
  simp only [variableKernelSeries, complexKernelSeries, PowerSeries.coeff_mk]
  have h_matrixEntryPolynomial_eval_complex (p : ℝ[X]) : MvPolynomial.eval₂ Complex.ofRealHom (fun ij : n × n => A ij.1 ij.2)
      (matrixEntryPolynomial p i j) = (aeval A p) i j := by
    rw [Polynomial.aeval_eq_sum_range]
    unfold matrixEntryPolynomial
    have h_variableMatrix_power_eval_complex (k : ℕ) (i : n) (j : n) : MvPolynomial.eval₂ Complex.ofRealHom (fun ij : n × n => A ij.1 ij.2)
        ((variableMatrix n ^ k) i j) = (A ^ k) i j := by
      induction k generalizing i j with
      | zero => simp only [pow_zero, Matrix.one_apply]; split_ifs <;> simp
      | succ k ih =>
        simp only [pow_succ, Matrix.mul_apply, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, ih]
        simp [variableMatrix]
    simp only [MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
      h_variableMatrix_power_eval_complex, Matrix.sum_apply, Matrix.smul_apply]
    simp only [Complex.real_smul, smul_eq_mul]
    rfl
  exact h_matrixEntryPolynomial_eval_complex _
def ofRealMatrixStarAlgHom : Matrix n n ℝ →⋆ₐ[ℝ] Matrix n n ℂ :=
  { Complex.ofRealHom.mapMatrix with
    commutes' := by
      intro a
      ext i j
      change ((if i = j then a else 0 : ℝ) : ℂ) = if i = j then ↑a else 0
      split_ifs <;> simp
    map_star' := by
      intro A
      ext i j
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply] }
theorem ofRealMatrixStarAlgHom_injective : Function.Injective (ofRealMatrixStarAlgHom (n := n)) := by
  intro A B h
  ext i j
  exact Complex.ofReal_injective (congrArg (fun M : Matrix n n ℂ => M i j) h)
theorem complexify_matrix_spectrum (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    spectrum ℝ (A.map Complex.ofReal) = spectrum ℝ A := by
  exact (Matrix.isHermitian_iff_isSelfAdjoint.mp hA).map_spectrum_real (ofRealMatrixStarAlgHom (n := n))
    ofRealMatrixStarAlgHom_injective
    (ofRealMatrixStarAlgHom (n := n)).toAlgHom.toLinearMap.continuous_of_finiteDimensional
end ComplexMatrices
section ComplexFreeCoordinates
open scoped Matrix.Norms.L2Operator
open RoughRegime.Upper RoughRegime.CombinedPolynomial RoughRegime.MatrixDeterminant
variable (r : ℕ) [NeZero r]
def complexParentValuation (A C : Matrix (Fin r) (Fin r) ℂ) : parentInverseVariables r → ℂ
  | Sum.inl ij => A ij.1 ij.2
  | Sum.inr ⟨_, ij⟩ => C ij.1 ij.2
theorem eval_renamed_series_complex  (f : V → W) (values : W → ℂ)
    (P : PowerSeries (MvPolynomial V ℝ)) :
    PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom values)
      (PowerSeries.map (MvPolynomial.rename f).toRingHom P) =
      PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (values ∘ f)) P := by
  ext k
  rw [PowerSeries.coeff_map, PowerSeries.coeff_map, PowerSeries.coeff_map]
  exact MvPolynomial.eval₂_rename _ _ _ _
theorem parentInverseEntryPolynomial_eval_complex (lo hi : ℝ)
    (A C : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (m : ℕ) :
    MvPolynomial.eval₂ Complex.ofRealHom (complexParentValuation r A C)
      (parentInverseEntryPolynomial lo hi r m i j) =
      ((intervalGeometricMean lo hi ^ (r + 1))⁻¹ : ℝ) *
        ∑ k ∈ Finset.range (m + 1),
          PowerSeries.coeff k (complexKernelSeries lo hi A i j * (complexKernelSeries lo hi C).det) := by
  have he : PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexParentValuation r A C))
      (combinedVariableSeries r (fun _ : Fin 1 => r) lo hi i j) =
      complexKernelSeries lo hi A i j * (complexKernelSeries lo hi C).det := by
    have h_inverseVariableSeries_eval_complex : PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexParentValuation r A C))
        (inverseVariableSeries r (fun _ : Fin 1 => r) lo hi i j) = complexKernelSeries lo hi A i j := by
      rw [inverseVariableSeries, eval_renamed_series_complex]
      exact congrArg (fun K => K i j) (variableKernelSeries_eval_complex lo hi A)
    have h_determinantVariableSeries_eval_complex (t : Fin 1) : PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (complexParentValuation r A C))
        (determinantVariableSeries r (fun _ : Fin 1 => r) lo hi t) =
        (complexKernelSeries lo hi C).det := by
      rw [determinantVariableSeries, eval_renamed_series_complex]
      change PowerSeries.map (MvPolynomial.eval₂Hom Complex.ofRealHom (fun ij : Fin r × Fin r => C ij.1 ij.2))
        (variableKernelSeries lo hi).det = _
      rw [RingHom.map_det, variableKernelSeries_eval_complex]
    simp only [combinedVariableSeries, map_mul, h_inverseVariableSeries_eval_complex, h_determinantVariableSeries_eval_complex, Fin.prod_univ_one]
  simp only [parentInverseEntryPolynomial, truncationEntryPolynomial, MvPolynomial.eval₂_mul,
    MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum, combinedCoefficientPolynomial]
  simp only [Fin.sum_univ_one]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hc := congrArg (fun P => PowerSeries.coeff k P) he
  rw [PowerSeries.coeff_map] at hc
  exact hc
end ComplexFreeCoordinates
section PolynomialBounds
variable {V : Type*} [Fintype V] [DecidableEq V]
def polynomialCoordinateBound (P : MvPolynomial V ℝ) (R : ℝ) : ℝ :=
  ∑ α ∈ P.support, ‖P.coeff α‖ * ∏ j : V, R ^ α j
theorem polynomialCoordinateBound_nonneg (P : MvPolynomial V ℝ) (R : ℝ) (hR : 0 ≤ R) :
    0 ≤ polynomialCoordinateBound P R := by
  unfold polynomialCoordinateBound
  positivity
theorem polynomial_complex_coordinate_bound (P : MvPolynomial V ℝ) (z : V → ℂ)
    (R : ℝ) (hR : 0 ≤ R) (hz : ∀ j, ‖z j‖ ≤ R) :
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
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (hz j) _
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
def incrementFinPolynomial (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ)
    (y : ℝ) (m : ℕ) (i : Fin r) :
    MvPolynomial (Fin (Fintype.card (incrementVariables r))) ℝ :=
  MvPolynomial.rename (Fintype.equivFin (incrementVariables r))
    (incrementEntryPolynomial r lo hi T y m i)
def currentRealCoordinateMatrix (u : incrementVariables r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => u (Sum.inl (Sum.inl (i, j)))
def parentRealCoordinateMatrix (u : incrementVariables r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => u (Sum.inl (Sum.inr ⟨0, (i, j)⟩))
end ActualDerivatives
section Similarity
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
def complexMatrixSimilarity (Q : (Matrix n n ℂ)ˣ) : Matrix n n ℂ →ₐ[ℝ] Matrix n n ℂ where
  toFun A := (Q : Matrix n n ℂ) * A * (↑Q⁻¹ : Matrix n n ℂ)
  map_one' := by simp
  map_mul' A B := by simp [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by rw [Algebra.algebraMap_eq_smul_one]; simp
theorem complexMatrixSimilarity_norm_le (Q : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    ‖complexMatrixSimilarity Q A‖ ≤ ‖(Q : Matrix n n ℂ)‖ * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ * ‖A‖ := by
  calc
    _ ≤ ‖(Q : Matrix n n ℂ) * A‖ * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ := norm_mul_le _ _
    _ ≤ ‖(Q : Matrix n n ℂ)‖ * ‖A‖ * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by ring
@[simp] theorem complexMatrixSimilarity_inverse (Q : (Matrix n n ℂ)ˣ) (A : Matrix n n ℂ) :
    complexMatrixSimilarity Q (complexMatrixSimilarity Q⁻¹ A) = A := by
  simp [complexMatrixSimilarity, Matrix.mul_assoc]
theorem normalizeMatrix_similarity (lo hi Q) (A : Matrix n n ℂ) :
    normalizeMatrix lo hi (complexMatrixSimilarity Q A) =
      complexMatrixSimilarity Q (normalizeMatrix lo hi A) := by
  simp [normalizeMatrix, map_sub, map_smul]
theorem similar_complex_kernel_coefficient_bound (lo hi ) (hlo : 0 < lo) (hlt : lo < hi)
    (A B ) (Q : (Matrix n n ℂ)ˣ) (χ : ℝ) (hχ : 0 ≤ χ)
    (hQ : ‖(Q : Matrix n n ℂ)‖ * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ ≤ χ)
    (hA : (complexMatrixSimilarity Q⁻¹ A).IsHermitian)
    (hSpec : spectrum ℝ (complexMatrixSimilarity Q⁻¹ A) ⊆ Set.Icc lo hi)
    (η δ : ℝ) (hη : 0 < η) (hη1 : η < 1) (hδ : 0 ≤ δ)
    (hsmall : 4 * δ * perturbationConstant η ≤ 1)
    (hd : χ * ‖normalizeMatrix lo hi B - normalizeMatrix lo hi A‖ ≤ δ) (k : ℕ) :
    ‖aeval B (kernelCoefficientPolynomial lo hi k)‖ ≤
      4 * χ * (intervalRho lo hi / η) ^ k := by
  have hc := complex_kernel_coefficient_bound lo hi hlo hlt
    (complexMatrixSimilarity Q⁻¹ A) (complexMatrixSimilarity Q⁻¹ B) hA hSpec
    η δ hη hη1 hδ hsmall (by rw [normalizeMatrix_similarity, normalizeMatrix_similarity, ← map_sub]; apply (complexMatrixSimilarity_norm_le Q⁻¹ _).trans; apply (mul_le_mul_of_nonneg_right _ (norm_nonneg _)).trans hd; simpa only [inv_inv, mul_comm] using hQ) k
  have he : aeval B (kernelCoefficientPolynomial lo hi k) =
      complexMatrixSimilarity Q (aeval (complexMatrixSimilarity Q⁻¹ B) (kernelCoefficientPolynomial lo hi k)) := by
    rw [← Polynomial.aeval_algHom_apply, complexMatrixSimilarity_inverse]
  rw [he]
  calc
    _ ≤ ‖(Q : Matrix n n ℂ)‖ * ‖(↑Q⁻¹ : Matrix n n ℂ)‖ *
        ‖aeval (complexMatrixSimilarity Q⁻¹ B) (kernelCoefficientPolynomial lo hi k)‖ :=
      complexMatrixSimilarity_norm_le _ _
    _ ≤ χ * (4 * (intervalRho lo hi / η) ^ k) := mul_le_mul hQ hc (norm_nonneg _) hχ
    _ = _ := by ring
end Similarity
section RealCharts
variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
theorem complexify_matrix_norm (A : Matrix n n ℝ) : ‖A.map Complex.ofReal‖ = ‖A‖ := by
  let φ := ofRealMatrixStarAlgHom (n := n)
  change ‖φ A‖ = ‖A‖
  have hs : IsSelfAdjoint (star A * A) := .star_mul_self A
  have hspec : spectrum ℝ (φ (star A * A)) = spectrum ℝ (star A * A) :=
    complexify_matrix_spectrum (star A * A) (Matrix.isHermitian_iff_isSelfAdjoint.mpr hs)
  have hgC := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (φ (star A * A)) (hs.map φ)
  rw [hspec] at hgC
  have he : ‖φ (star A * A)‖ = ‖star A * A‖ := hgC.unique (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (star A * A) hs)
  have hm : φ (star A * A) = star (φ A) * φ A := by rw [map_mul, map_star]
  rw [hm, CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at he
  exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp he
def complexifyMatrixUnit (Q : (Matrix n n ℝ)ˣ) : (Matrix n n ℂ)ˣ :=
  Units.map Complex.ofRealHom.mapMatrix.toMonoidHom Q
@[simp] theorem complexifyMatrixUnit_coe (Q : (Matrix n n ℝ)ˣ) :
    (complexifyMatrixUnit Q : Matrix n n ℂ) = (Q : Matrix n n ℝ).map Complex.ofReal := rfl
@[simp] theorem complexifyMatrixUnit_inv (Q : (Matrix n n ℝ)ˣ) :
    complexifyMatrixUnit Q⁻¹ = (complexifyMatrixUnit Q)⁻¹ := by
  rfl
theorem complexifyMatrixUnit_condition (Q : (Matrix n n ℝ)ˣ) :
    ‖(complexifyMatrixUnit Q : Matrix n n ℂ)‖ * ‖(↑(complexifyMatrixUnit Q)⁻¹ : Matrix n n ℂ)‖ =
      ‖(Q : Matrix n n ℝ)‖ * ‖(↑Q⁻¹ : Matrix n n ℝ)‖ := by
  rw [← complexifyMatrixUnit_inv, complexifyMatrixUnit_coe, complexifyMatrixUnit_coe,
    complexify_matrix_norm, complexify_matrix_norm]
theorem complexify_matrix_similarity (Q : (Matrix n n ℝ)ˣ) (A : Matrix n n ℝ) :
    complexMatrixSimilarity (complexifyMatrixUnit Q) (A.map Complex.ofReal) =
      (matrixSimilarity Q A).map Complex.ofReal := by
  change _ * _ * _ = ((Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ)).map Complex.ofReal
  rw [← complexifyMatrixUnit_inv, complexifyMatrixUnit_coe, complexifyMatrixUnit_coe]
  change Complex.ofRealHom.mapMatrix (Q : Matrix n n ℝ) * Complex.ofRealHom.mapMatrix A *
    Complex.ofRealHom.mapMatrix (↑Q⁻¹ : Matrix n n ℝ) =
    Complex.ofRealHom.mapMatrix ((Q : Matrix n n ℝ) * A * (↑Q⁻¹ : Matrix n n ℝ))
  rw [map_mul, map_mul]
end RealCharts
section Neighborhood
variable (r : ℕ) [NeZero r]
def similarInverseCoordinateRadius (lo hi η χ : ℝ) : ℝ :=
  min 1 ((4 * perturbationConstant η)⁻¹ /
    (χ * max 1 (|(intervalHalfWidth lo hi)⁻¹| *
      (‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖))))
theorem similarInverseCoordinateRadius_pos (lo hi η χ )
    (hη : 0 < η) (hη1 : η < 1) (hχ : 0 < χ) :
    0 < similarInverseCoordinateRadius r lo hi η χ := by
  have := perturbationConstant_pos η hη hη1
  apply lt_min (by norm_num)
  apply div_pos (by positivity)
  apply mul_pos hχ
  exact (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _)
theorem coordinate_similar_perturbation (lo hi η χ ) (hχ : 0 < χ)
    (z z₀ )
    (hz : ‖z - z₀‖ < similarInverseCoordinateRadius r lo hi η χ)
    (F : (incrementVariables r → ℂ) →L[ℂ] Matrix (Fin r) (Fin r) ℂ)
    (hF : ‖F‖ ≤ ‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖) :
    χ * ‖normalizeMatrix lo hi (F z) - normalizeMatrix lo hi (F z₀)‖ ≤
      (4 * perturbationConstant η)⁻¹ := by
  let D := max 1 (|(intervalHalfWidth lo hi)⁻¹| *
    (‖currentCoordinateCLM r‖ + ‖parentCoordinateCLM r‖))
  have hD : 0 < D := (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _)
  have hz' : ‖z - z₀‖ ≤ (4 * perturbationConstant η)⁻¹ / (χ * D) :=
    hz.le.trans (min_le_right _ _)
  rw [normalizeMatrix_sub, norm_smul, Real.norm_eq_abs, ← map_sub]
  calc
    _ ≤ χ * (|(intervalHalfWidth lo hi)⁻¹| * (‖F‖ * ‖z - z₀‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (F.le_opNorm _) (abs_nonneg _)) hχ.le
    _ ≤ χ * D * ‖z - z₀‖ := by
      have hc : |(intervalHalfWidth lo hi)⁻¹| * ‖F‖ ≤ D :=
        (mul_le_mul_of_nonneg_left hF (abs_nonneg _)).trans (le_max_right _ _)
      have hh := mul_le_mul_of_nonneg_right hc (mul_nonneg hχ.le (norm_nonneg (z - z₀)))
      nlinarith only [hh]
    _ ≤ _ := by simpa only [mul_comm] using (le_div_iff₀ (mul_pos hχ hD)).mp hz'
def similarInverseEnvelope (lo hi q χ : ℝ) : ℝ :=
  |(intervalGeometricMean lo hi ^ (r + 1))⁻¹| *
    (Fintype.card (Equiv.Perm (Fin r)) : ℝ) * (4 * χ) ^ (r + 1) *
    ∑' k : ℕ, ((k + 1 ) : ℝ) ^ (r + 1) * q ^ k
def boundedNumeratorEnvelope (L Y : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  ∑ j : Fin r, (
    polynomialCoordinateBound (rawNumeratorPolynomial r T false j) (L + 1) +
      Y * polynomialCoordinateBound (rawNumeratorPolynomial r T true j) (L + 1))
def similarIncrementEnvelope (lo hi q χ L Y : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  similarInverseEnvelope r lo hi q χ * boundedNumeratorEnvelope r L Y T
theorem similarInverseEnvelope_nonneg (lo hi q χ ) (hq : 0 ≤ q) (hχ : 0 ≤ χ) :
    0 ≤ similarInverseEnvelope r lo hi q χ := by
  apply mul_nonneg (by positivity)
  exact tsum_nonneg (fun k => by positivity)
theorem actual_similar_increment_complex_neighborhood (lo hi ) (hlo : 0 < lo) (hlt : lo < hi)
    (η ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ ) (hχ : 0 < χ) (L Y ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T y) (hy : |y| ≤ Y)
    (z₀ z : incrementVariables r → ℂ) (hz₀ : ‖z₀‖ ≤ L)
    (Q S : (Matrix (Fin r) (Fin r) ℂ)ˣ)
    (hQ : ‖(Q : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ)
    (hS : ‖(S : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑S⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ)
    (hA : (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r z₀)).IsHermitian)
    (hC : (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r z₀)).IsHermitian)
    (hASpec : spectrum ℝ (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r z₀)) ⊆ Set.Icc lo hi)
    (hCSpec : spectrum ℝ (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r z₀)) ⊆ Set.Icc lo hi)
    (hz : ‖z - z₀‖ < similarInverseCoordinateRadius r lo hi η χ) (m : ℕ) (i : Fin r) :
    ‖MvPolynomial.eval₂ Complex.ofRealHom z (incrementEntryPolynomial r lo hi T y m i)‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T := by
  have hρ := intervalRho_pos lo hi hlo hlt
  have hη : 0 < η := hρ.trans hρη
  have hq : 0 < intervalRho lo hi / η := div_pos hρ hη
  have hδ : 0 ≤ (4 * perturbationConstant η)⁻¹ :=
    (inv_pos.mpr (mul_pos (by norm_num) (perturbationConstant_pos η hη hη1))).le
  have hsmall : 4 * (4 * perturbationConstant η)⁻¹ * perturbationConstant η ≤ 1 := by
    have hK := ne_of_gt (perturbationConstant_pos η hη hη1)
    field_simp
    norm_num
  have hdA := coordinate_similar_perturbation r lo hi η χ hχ z z₀ hz
    (currentCoordinateCLM r) (le_add_of_nonneg_right (norm_nonneg _))
  have hdC := coordinate_similar_perturbation r lo hi η χ hχ z z₀ hz
    (parentCoordinateCLM r) (le_add_of_nonneg_left (norm_nonneg _))
  have hK (a b : Fin r) (k : ℕ) :
      ‖PowerSeries.coeff k (complexKernelSeries lo hi (currentCoordinateCLM r z) a b)‖ ≤
        4 * χ * (intervalRho lo hi / η) ^ k := by
    simp only [complexKernelSeries, PowerSeries.coeff_mk]
    exact (matrix_entry_norm_le_l2 _ a b).trans
      (similar_complex_kernel_coefficient_bound lo hi hlo hlt _ _ Q χ hχ.le hQ hA hASpec
        η _ hη hη1 hδ hsmall hdA k)
  have hD (a b : Fin r) (k : ℕ) :
      ‖PowerSeries.coeff k (complexKernelSeries lo hi (parentCoordinateCLM r z) a b)‖ ≤
        4 * χ * (intervalRho lo hi / η) ^ k := by
    simp only [complexKernelSeries, PowerSeries.coeff_mk]
    exact (matrix_entry_norm_le_l2 _ a b).trans
      (similar_complex_kernel_coefficient_bound lo hi hlo hlt _ _ S χ hχ.le hS hC hCSpec
        η _ hη hη1 hδ hsmall hdC k)
  have hzR : ∀ j, ‖z j‖ ≤ L + 1 := by
    intro j
    apply (norm_le_pi_norm z j).trans
    calc
      ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + L := add_le_add (hz.le.trans (min_le_left _ _)) hz₀
      _ = _ := by ring
  have hI (j : Fin r) :
      ‖MvPolynomial.eval₂ Complex.ofRealHom z
        (MvPolynomial.rename Sum.inl (parentInverseEntryPolynomial lo hi r m i j))‖ ≤
        similarInverseEnvelope r lo hi (intervalRho lo hi / η) χ := by
    have h_coordinate_parent_valuation : z ∘ Sum.inl = complexParentValuation r (currentCoordinateCLM r z) (parentCoordinateCLM r z) := by
      funext v
      cases v with
      | inl ij => rfl
      | inr t =>
        rcases t with ⟨t, ij⟩
        have : t = 0 := Subsingleton.elim _ _
        subst t
        rfl
    rw [MvPolynomial.eval₂_rename, h_coordinate_parent_valuation,
      parentInverseEntryPolynomial_eval_complex, norm_mul, Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left
      (combined_truncation_uniform_bound _ _ _ (4 * χ) hq ((div_lt_one hη).mpr hρη) (by positivity) hK hD i j m)
      (abs_nonneg _)).trans_eq (by simp [similarInverseEnvelope, mul_assoc])
  simp only [incrementEntryPolynomial, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul]
  calc
    _ ≤ ∑ j : Fin r, ‖MvPolynomial.eval₂ Complex.ofRealHom z
        (MvPolynomial.rename Sum.inl (parentInverseEntryPolynomial lo hi r m i j)) *
        MvPolynomial.eval₂ Complex.ofRealHom z (numeratorPolynomial r T y j)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin r, similarInverseEnvelope r lo hi (intervalRho lo hi / η) χ *
        (polynomialCoordinateBound (rawNumeratorPolynomial r T false j) (L + 1) +
          Y * polynomialCoordinateBound (rawNumeratorPolynomial r T true j) (L + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      have h_bounded_numerator_complex_bound : ‖MvPolynomial.eval₂ Complex.ofRealHom z (numeratorPolynomial r T y j)‖ ≤
          polynomialCoordinateBound (rawNumeratorPolynomial r T false j) (L + 1) +
            Y * polynomialCoordinateBound (rawNumeratorPolynomial r T true j) (L + 1) := by
        simp only [numeratorPolynomial, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C]
        calc
          _ ≤ ‖MvPolynomial.eval₂ Complex.ofRealHom z (rawNumeratorPolynomial r T false j)‖ +
              ‖Complex.ofRealHom y * MvPolynomial.eval₂ Complex.ofRealHom z (rawNumeratorPolynomial r T true j)‖ :=
            norm_sub_le _ _
          _ ≤ _ := by
            apply add_le_add (polynomial_complex_coordinate_bound _ z _ (by positivity) hzR)
            rw [norm_mul]
            change ‖(y : ℂ)‖ * _ ≤ _
            rw [Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul hy (polynomial_complex_coordinate_bound _ z _ (by positivity) hzR)
              (norm_nonneg _) hY
      exact mul_le_mul (hI j) h_bounded_numerator_complex_bound
        (norm_nonneg _) (similarInverseEnvelope_nonneg r lo hi _ χ hq.le hχ.le)
    _ = _ := by rw [← Finset.mul_sum]; rfl
end Neighborhood
section Derivatives
open RoughRegime.ComplexDerivativeBridge
variable (r : ℕ) [NeZero r]
theorem norm_reindex_le  [Fintype V] [Fintype W]
    (z : V → ℂ) (f : W → V) : ‖z ∘ f‖ ≤ ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro j
  exact norm_le_pi_norm z (f j)
theorem actual_similar_increment_derivative_bound (lo hi ) (hlo : 0 < lo) (hlt : lo < hi)
    (η ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ ) (hχ : 0 < χ) (L Y ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T y) (hy : |y| ≤ Y)
    (u : incrementVariables r → ℝ) (hu : ‖u‖ ≤ L)
    (Q S : (Matrix (Fin r) (Fin r) ℂ)ˣ)
    (hQ : ‖(Q : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ)
    (hS : ‖(S : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑S⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ)
    (hA : (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (u j : ℂ)))).IsHermitian)
    (hC : (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (u j : ℂ)))).IsHermitian)
    (hASpec : spectrum ℝ (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (u j : ℂ)))) ⊆ Set.Icc lo hi)
    (hCSpec : spectrum ℝ (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (u j : ℂ)))) ⊆ Set.Icc lo hi)
    (m k : ℕ) (hk : 0 < k) (i : Fin r)
    (v : Fin k → Fin (Fintype.card (incrementVariables r)) → ℝ) :
    ‖iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i))
      (fun j => u ((Fintype.equivFin (incrementVariables r)).symm j)) v‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T * ↑k.factorial *
        (Real.exp 1 / similarInverseCoordinateRadius r lo hi η χ) ^ k * ∏ j, ‖v j‖ := by
  let uFin := fun j => u ((Fintype.equivFin (incrementVariables r)).symm j)
  let z₀ : incrementVariables r → ℂ := fun j => (u j : ℂ)
  have hz₀ : ‖z₀‖ ≤ L := by
    apply (pi_norm_le_iff_of_nonneg hL).mpr
    intro j
    have hj : ‖z₀ j‖ ≤ ‖u‖ := by simpa [z₀] using norm_le_pi_norm u j
    exact hj.trans hu
  apply real_polynomial_derivative_bound _ uFin _ _
    (similarInverseCoordinateRadius_pos r lo hi η χ ((intervalRho_pos lo hi hlo hlt).trans hρη) hη1 hχ) _ hk v
  intro z hz
  rw [complexify, MvPolynomial.eval_map, incrementFinPolynomial, MvPolynomial.eval₂_rename]
  apply actual_similar_increment_complex_neighborhood r lo hi hlo hlt η hρη hη1 χ hχ L Y hL hY T y hy
    z₀ (z ∘ Fintype.equivFin (incrementVariables r)) hz₀ Q S hQ hS hA hC hASpec hCSpec _ m i
  have he : z ∘ Fintype.equivFin (incrementVariables r) - z₀ =
      (z - (fun j => (uFin j : ℂ))) ∘ Fintype.equivFin (incrementVariables r) := by
    funext j
    simp [z₀, uFin]
  rw [he]
  exact (norm_reindex_le _ _).trans_lt hz
end Derivatives
section PaperEndpoint
variable (r : ℕ) [NeZero r]
structure InverseDerivativeCenter (lo hi χ L : ℝ) where
  moments : incrementVariables r → ℝ
  normBound : ‖moments‖ ≤ L
  currentChart : (Matrix (Fin r) (Fin r) ℝ)ˣ
  parentChart : (Matrix (Fin r) (Fin r) ℝ)ˣ
  currentCondition : ‖(currentChart : Matrix (Fin r) (Fin r) ℝ)‖ *
    ‖(↑currentChart⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ
  parentCondition : ‖(parentChart : Matrix (Fin r) (Fin r) ℝ)‖ *
    ‖(↑parentChart⁻¹ : Matrix (Fin r) (Fin r) ℝ)‖ ≤ χ
  currentHermitian : (matrixSimilarity currentChart⁻¹ (currentRealCoordinateMatrix r moments)).IsHermitian
  parentHermitian : (matrixSimilarity parentChart⁻¹ (parentRealCoordinateMatrix r moments)).IsHermitian
  currentSpectrum : spectrum ℝ (matrixSimilarity currentChart⁻¹ (currentRealCoordinateMatrix r moments)) ⊆ Set.Icc lo hi
  parentSpectrum : spectrum ℝ (matrixSimilarity parentChart⁻¹ (parentRealCoordinateMatrix r moments)) ⊆ Set.Icc lo hi
def inverseDerivativeRate (lo hi η χ : ℝ) : ℝ :=
  Real.exp 1 / similarInverseCoordinateRadius r lo hi η χ
theorem inverseDerivativeRate_pos (lo hi η χ ) (hη : 0 < η) (hη1 : η < 1) (hχ : 0 < χ) :
    0 < inverseDerivativeRate r lo hi η χ :=
  div_pos (Real.exp_pos _) (similarInverseCoordinateRadius_pos r lo hi η χ hη hη1 hχ)
theorem similarIncrementEnvelope_nonneg (lo hi q χ L Y )
    (hq : 0 ≤ q) (hχ : 0 ≤ χ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T ) : 0 ≤ similarIncrementEnvelope r lo hi q χ L Y T := by
  apply mul_nonneg (similarInverseEnvelope_nonneg r lo hi q χ hq hχ)
  exact Finset.sum_nonneg (fun j hj => add_nonneg
    (polynomialCoordinateBound_nonneg _ _ (by positivity))
    (mul_nonneg hY (polynomialCoordinateBound_nonneg _ _ (by positivity))))
theorem paper_inverse_derivative_bound (lo hi ) (hlo : 0 < lo) (hlt : lo < hi)
    (η ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ ) (hχ : 0 < χ) (L Y ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T y) (hy : |y| ≤ Y)
    (c : InverseDerivativeCenter r lo hi χ L) (m k : ℕ) (i v) :
    ‖iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i))
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T * ↑k.factorial *
        inverseDerivativeRate r lo hi η χ ^ k * ∏ j, ‖v j‖ := by
  let Q := complexifyMatrixUnit c.currentChart
  let S := complexifyMatrixUnit c.parentChart
  have hQ : ‖(Q : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑Q⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ := by
    rw [complexifyMatrixUnit_condition]
    exact c.currentCondition
  have hS : ‖(S : Matrix (Fin r) (Fin r) ℂ)‖ * ‖(↑S⁻¹ : Matrix (Fin r) (Fin r) ℂ)‖ ≤ χ := by
    rw [complexifyMatrixUnit_condition]
    exact c.parentCondition
  have hAeq : complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (c.moments j ))) =
      (matrixSimilarity c.currentChart⁻¹ (currentRealCoordinateMatrix r c.moments)).map Complex.ofReal := by
    change complexMatrixSimilarity (complexifyMatrixUnit c.currentChart)⁻¹
      ((currentRealCoordinateMatrix r c.moments).map Complex.ofReal) = _
    rw [← complexifyMatrixUnit_inv, complexify_matrix_similarity]
  have hCeq : complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (c.moments j : ℂ))) =
      (matrixSimilarity c.parentChart⁻¹ (parentRealCoordinateMatrix r c.moments)).map Complex.ofReal := by
    change complexMatrixSimilarity (complexifyMatrixUnit c.parentChart)⁻¹
      ((parentRealCoordinateMatrix r c.moments).map Complex.ofReal) = _
    rw [← complexifyMatrixUnit_inv, complexify_matrix_similarity]
  have hA : (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (c.moments j : ℂ)))).IsHermitian := by
    rw [hAeq]
    exact c.currentHermitian.map _ (fun x => by simp)
  have hC : (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (c.moments j )))).IsHermitian := by
    rw [hCeq]
    exact c.parentHermitian.map _ (fun x => by simp)
  have hASpec : spectrum ℝ (complexMatrixSimilarity Q⁻¹ (currentCoordinateCLM r (fun j => (c.moments j )))) ⊆ Set.Icc lo hi := by
    rw [hAeq, complexify_matrix_spectrum _ c.currentHermitian]
    exact c.currentSpectrum
  have hCSpec : spectrum ℝ (complexMatrixSimilarity S⁻¹ (parentCoordinateCLM r (fun j => (c.moments j )))) ⊆ Set.Icc lo hi := by
    rw [hCeq, complexify_matrix_spectrum _ c.parentHermitian]
    exact c.parentSpectrum
  cases k with
  | zero =>
    simp only [iteratedFDeriv_zero_apply, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one,
      Fin.prod_univ_zero, incrementFinPolynomial, MvPolynomial.eval_rename]
    have he : (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) ∘
      Fintype.equivFin (incrementVariables r) = c.moments := by funext j; simp
    rw [he]
    have hz : ‖(fun j => (c.moments j : ℂ))‖ ≤ L := by
      apply (pi_norm_le_iff_of_nonneg hL).mpr
      intro j
      have hj : ‖(c.moments j : ℂ)‖ ≤ ‖c.moments‖ := by simpa using norm_le_pi_norm c.moments j
      exact hj.trans c.normBound
    have hc := actual_similar_increment_complex_neighborhood r lo hi hlo hlt η hρη hη1 χ hχ L Y hL hY T y hy
      (fun j => (c.moments j : ℂ)) (fun j => (c.moments j : ℂ)) hz Q S hQ hS hA hC hASpec hCSpec
      (by simpa using similarInverseCoordinateRadius_pos r lo hi η χ ((intervalRho_pos lo hi hlo hlt).trans hρη) hη1 hχ) m i
    have he : MvPolynomial.eval₂ Complex.ofRealHom (fun j => (c.moments j : ℂ))
        (incrementEntryPolynomial r lo hi T y m i) =
        (MvPolynomial.eval c.moments (incrementEntryPolynomial r lo hi T y m i) : ℂ) :=
      (MvPolynomial.eval₂_comp Complex.ofRealHom c.moments _).symm
    rw [he, Complex.norm_real] at hc
    exact hc
  | succ k =>
    exact actual_similar_increment_derivative_bound r lo hi hlo hlt η hρη hη1 χ hχ L Y hL hY
      T y hy c.moments c.normBound Q S hQ hS hA hC hASpec hCSpec m (k + 1) (by omega) i v
def incrementFinVector (lo hi : ℝ) (T : Matrix (Fin r) (Fin r) ℝ) (y : ℝ) (m : ℕ) :
    (Fin (Fintype.card (incrementVariables r)) → ℝ) → Fin r → ℝ :=
  fun x i => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i)
theorem incrementFinVector_contDiff (lo hi T y m) :
    ContDiff ℝ ⊤ (incrementFinVector r lo hi T y m) :=
  contDiff_pi.mpr (fun i => RoughRegime.PolynomialDerivatives.polynomial_contDiff _)
theorem paper_inverse_vector_derivative_bound (lo hi ) (hlo : 0 < lo) (hlt : lo < hi)
    (η ) (hρη : intervalRho lo hi < η) (hη1 : η < 1)
    (χ ) (hχ : 0 < χ) (L Y ) (hL : 0 ≤ L) (hY : 0 ≤ Y)
    (T y) (hy : |y| ≤ Y)
    (c : InverseDerivativeCenter r lo hi χ L) (m k : ℕ)
    (v ) :
    ‖iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m)
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v‖ ≤
      similarIncrementEnvelope r lo hi (intervalRho lo hi / η) χ L Y T * k.factorial *
        inverseDerivativeRate r lo hi η χ ^ k * ∏ j, ‖v j‖ := by
  have hη  := (intervalRho_pos lo hi hlo hlt).trans hρη
  have := similarIncrementEnvelope_nonneg r lo hi _ χ L Y
    (div_pos (intervalRho_pos lo hi hlo hlt) hη).le hχ.le hL hY T
  have := inverseDerivativeRate_pos r lo hi η χ hη hη1 hχ
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hd := (ContinuousLinearMap.proj i : (Fin r → ℝ) →L[ℝ] ℝ).iteratedFDeriv_comp_left
    (x := fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j))
    (incrementFinVector_contDiff r lo hi T y m).contDiffAt (show (k : WithTop ℕ∞) ≤ ⊤ from le_top)
  have he := congrArg (fun D => D v) hd
  change iteratedFDeriv ℝ k (fun x => MvPolynomial.eval x (incrementFinPolynomial r lo hi T y m i))
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v =
    (iteratedFDeriv ℝ k (incrementFinVector r lo hi T y m)
      (fun j => c.moments ((Fintype.equivFin (incrementVariables r)).symm j)) v) i at he
  rw [← he]
  exact paper_inverse_derivative_bound r lo hi hlo hlt η hρη hη1 χ hχ L Y hL hY T y hy c m k i v
end PaperEndpoint
end NearlyMinimax
end
open MeasureTheory Set Matrix MvPolynomial
open scoped BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
namespace NearlyMinimax
variable {d ℓ : ℕ}
abbrev AnchoredCoefficientSpace (d ℓ : ℕ) := EuclideanSpace ℝ (AnchoredIndex d ℓ)
def anchoredQuadratic  (u : Covariate d) (c : AnchoredCoefficientSpace d ℓ) : ℝ :=
  c.ofLp ⬝ᵥ (anchoredGram u *ᵥ c.ofLp)
theorem anchoredGram_entry_continuous  (γ δ : AnchoredIndex d ℓ) :
    Continuous (fun u => anchoredGram u γ δ) := by
  exact continuous_parametric_integral_of_continuous
    ((anchoredFeature_continuous γ).mul (anchoredFeature_continuous δ))
    (unitCube_isCompact d)
theorem anchoredQuadratic_continuous  :
    Continuous (fun z : Covariate d × AnchoredCoefficientSpace d ℓ =>
      anchoredQuadratic z.1 z.2) := by
  change Continuous (fun z : Covariate d × AnchoredCoefficientSpace d ℓ =>
    ∑ γ, z.2 γ * ∑ δ, anchoredGram z.1 γ δ * z.2 δ)
  apply continuous_finset_sum
  intro γ hγ
  apply Continuous.mul ((PiLp.continuous_apply 2 _ γ).comp continuous_snd)
  apply continuous_finset_sum
  intro δ hδ
  exact ((anchoredGram_entry_continuous γ δ).comp continuous_fst).mul
    ((PiLp.continuous_apply 2 _ δ).comp continuous_snd)
theorem anchoredQuadratic_pos  (u : Covariate d)
    (c : AnchoredCoefficientSpace d ℓ) (hc : c ≠ 0) : 0 < anchoredQuadratic u c := by
  simpa only [star_trivial, anchoredQuadratic] using ((anchoredGram_posDef (ℓ := ℓ) u).dotProduct_mulVec_pos (by intro h; apply hc; exact PiLp.ext (fun i => congrFun h i)))
theorem anchoredIndex_nonempty  (hd : 0 < d) (hℓ : 0 < ℓ) :
    Nonempty (AnchoredIndex d ℓ) := by
  let γ : PolynomialBox d ℓ := fun i => if i = (⟨0, hd⟩) then ⟨1, by omega⟩ else 0
  have hs : (∑ i, (γ i).val) = 1 := by
    simp only [γ, apply_ite]
    simp
  exact ⟨⟨γ, by rw [hs]; exact ⟨by norm_num, hℓ⟩⟩⟩
def anchoredDensityGram  (u : Covariate d) (p : Covariate d → ℝ) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  fun γ δ => ∫ w, p w * (anchoredFeature u w γ * anchoredFeature u w δ) ∂cubeVolume d
theorem anchoredDensityGram_isHermitian  (u : Covariate d)
    (p : Covariate d → ℝ) : (anchoredDensityGram (ℓ := ℓ) u p).IsHermitian := by
  ext γ δ
  simp only [conjTranspose_apply, star_trivial, anchoredDensityGram]
  congr 1
  funext w
  rw [mul_comm (anchoredFeature u w δ) (anchoredFeature u w γ)]
theorem anchoredDensityGram_product_integrable  (u p) (hpmeas : Measurable p) (b )
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) (γ δ : AnchoredIndex d ℓ) :
    Integrable (fun w => p w * (anchoredFeature u w γ * anchoredFeature u w δ))
      (cubeVolume d) := by
  apply (anchoredFeature_product_integrable u γ δ).bdd_mul hpmeas.aestronglyMeasurable
  exact hp.mono (fun w hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2)
theorem anchoredDensityGram_quadratic_bounds  (u p) (hpmeas : Measurable p) (a b ) (ha : 0 ≤ a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) (c : AnchoredIndex d ℓ → ℝ) :
    a * c ⬝ᵥ (anchoredGram u *ᵥ c) ≤ c ⬝ᵥ (anchoredDensityGram u p *ᵥ c) ∧
      c ⬝ᵥ (anchoredDensityGram u p *ᵥ c) ≤ b * (c ⬝ᵥ (anchoredGram u *ᵥ c)) := by
  have hp0 : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b :=
    hp.mono (fun w hw => ⟨ha.trans hw.1, hw.2⟩)
  let f : Covariate d → ℝ := fun w => (∑ γ, c γ * anchoredFeature u w γ) ^ 2
  have hf : Continuous f := by
    unfold f
    apply Continuous.pow
    apply continuous_finset_sum
    intro γ hγ
    exact ((anchoredMonomial_continuous γ).comp
      (continuous_id.sub continuous_const)).const_mul (c γ)
  have hi : Integrable f (cubeVolume d) :=
    ContinuousOn.integrableOn_compact (unitCube_isCompact d) hf.continuousOn
  have hpi : Integrable (fun w => p w * f w) (cubeVolume d) := by
    apply hi.bdd_mul hpmeas.aestronglyMeasurable
    exact hp0.mono (fun w hw => by rw [Real.norm_eq_abs, abs_of_nonneg hw.1]; exact hw.2)
  have h_anchoredDensityGram_quadratic (c : AnchoredIndex d ℓ → ℝ) : c ⬝ᵥ (anchoredDensityGram u p *ᵥ c) =
      ∫ w, p w * (∑ γ, c γ * anchoredFeature u w γ) ^ 2 ∂cubeVolume d := by
    classical
    have heq : (fun w => p w * (∑ γ, c γ * anchoredFeature u w γ) ^ 2) =
        (fun w => ∑ γ, ∑ δ, c γ *
          (p w * (anchoredFeature u w γ * anchoredFeature u w δ)) * c δ) := by
      funext w
      rw [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro δ hδ
      ring
    rw [heq, integral_finset_sum]
    · change (∑ γ, c γ * ∑ δ, anchoredDensityGram u p γ δ * c δ) = _
      simp only [Finset.mul_sum, anchoredDensityGram]
      apply Finset.sum_congr rfl
      intro γ hγ
      rw [integral_finset_sum]
      · simp_rw [integral_mul_const, integral_const_mul]
        apply Finset.sum_congr rfl
        intro δ hδ
        ring
      · intro δ hδ
        exact ((anchoredDensityGram_product_integrable u p hpmeas b hp0 γ δ).const_mul
          (c γ)).mul_const (c δ)
    · intro γ hγ
      exact integrable_finset_sum _ (fun δ hδ =>
        ((anchoredDensityGram_product_integrable u p hpmeas b hp0 γ δ).const_mul
          (c γ)).mul_const (c δ))
  rw [anchoredGram_quadratic, h_anchoredDensityGram_quadratic,
    ← integral_const_mul, ← integral_const_mul]
  constructor
  · exact integral_mono_ae (hi.const_mul a) hpi (hp.mono (fun w hw =>
      mul_le_mul_of_nonneg_right hw.1 (sq_nonneg _)))
  · exact integral_mono_ae hpi (hi.const_mul b) (hp.mono (fun w hw =>
      mul_le_mul_of_nonneg_right hw.2 (sq_nonneg _)))
def anchoredWhitening  (u : Covariate d) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  (CFC.sqrt (anchoredGram u))⁻¹
theorem anchoredGram_sqrt_isUnit  (u : Covariate d) :
    IsUnit (CFC.sqrt (anchoredGram (ℓ := ℓ) u)) :=
  (CFC.isUnit_sqrt_iff _ (anchoredGram_posDef u).posSemidef.nonneg).mpr
    (anchoredGram_posDef u).isUnit
theorem anchoredWhitening_isHermitian  (u : Covariate d) :
    (anchoredWhitening (ℓ := ℓ) u).IsHermitian :=
  (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg (anchoredGram u))).isHermitian.inv
def anchoredWhitenedGram  (u : Covariate d) (p : Covariate d → ℝ) :
    Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ :=
  anchoredWhitening u * anchoredDensityGram u p * anchoredWhitening u
theorem anchoredWhitenedGram_isHermitian  (u : Covariate d)
    (p : Covariate d → ℝ) : (anchoredWhitenedGram (ℓ := ℓ) u p).IsHermitian := by
  have h := Matrix.isHermitian_conjTranspose_mul_mul (anchoredWhitening (ℓ := ℓ) u)
    (anchoredDensityGram_isHermitian u p)
  rw [(anchoredWhitening_isHermitian u).eq] at h
  exact h
def anchoredSimilarityUnit  (u : Covariate d) :
    (Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ)ˣ :=
  (anchoredGram_sqrt_isUnit (ℓ := ℓ) u).unit⁻¹
@[simp] theorem anchoredSimilarityUnit_val  (u : Covariate d) :
    (anchoredSimilarityUnit (ℓ := ℓ) u).val = anchoredWhitening u := by
  rw [anchoredSimilarityUnit, Matrix.coe_units_inv, IsUnit.unit_spec]
  rfl
@[simp] theorem anchoredSimilarityUnit_inv_val  (u : Covariate d) :
    ((anchoredSimilarityUnit (ℓ := ℓ) u)⁻¹).val = CFC.sqrt (anchoredGram u) := by
  simp only [anchoredSimilarityUnit, inv_inv, IsUnit.unit_spec]
theorem anchoredWhitening_square  (u : Covariate d) :
    (anchoredGram (ℓ := ℓ) u)⁻¹ = anchoredWhitening u * anchoredWhitening u := by
  calc
    (anchoredGram u)⁻¹ = (CFC.sqrt (anchoredGram u) * CFC.sqrt (anchoredGram u))⁻¹ :=
      congrArg Inv.inv (CFC.sqrt_mul_sqrt_self (anchoredGram u)
        (anchoredGram_posDef u).posSemidef.nonneg).symm
    _ = _ := Matrix.mul_inv_rev _ _
theorem anchoredGram_continuous  :
    Continuous (anchoredGram (d := d) (ℓ := ℓ)) :=
  continuous_matrix anchoredGram_entry_continuous
theorem anchoredGram_sqrt_continuous  :
    Continuous (fun u : Covariate d => CFC.sqrt (anchoredGram (ℓ := ℓ) u)) := by
  exact CFC.continuousOn_sqrt.comp_continuous anchoredGram_continuous
    (fun u => (anchoredGram_posDef u).posSemidef.nonneg)
theorem anchoredWhitening_continuous  :
    Continuous (anchoredWhitening (d := d) (ℓ := ℓ)) := by
  rw [continuous_iff_continuousAt]
  intro u
  exact (continuousAt_matrix_inv _ (by have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext Ring.inverse_eq_inv; rw [heq]; exact continuousAt_inv₀ ((Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)).ne_zero)).comp (f := fun v : Covariate d => CFC.sqrt (anchoredGram (ℓ := ℓ) v))
    (x := u) ((anchoredGram_sqrt_continuous).continuousAt (x := u))
def anchoredVectorMoment  (u : Covariate d)
    (p g : Covariate d → ℝ) : AnchoredIndex d ℓ → ℝ :=
  fun γ => ∫ w, p w * anchoredFeature u w γ * g w ∂cubeVolume d
def anchoredPreconditionedMoment  (u : Covariate d)
    (p g : Covariate d → ℝ) : AnchoredIndex d ℓ → ℝ :=
  (anchoredGram u)⁻¹ *ᵥ anchoredVectorMoment u p g
theorem anchoredVectorMoment_norm_bound  (u )
    (hu : u ∈ unitCube d) (p g ) (b F : ℝ)
    (hb : 0 ≤ b) (hF : 0 ≤ F)
    (hp : ∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b)
    (hg : ∀ w ∈ unitCube d, |g w| ≤ F) :
    ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredVectorMoment u p g)‖ ≤
      Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (b * F) := by
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_iff]
  constructor
  · exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg hb hF)
  · calc
      (∑ γ : AnchoredIndex d ℓ, ‖((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredVectorMoment u p g)) γ‖ ^ 2) ≤ ∑ _γ : AnchoredIndex d ℓ, (b * F) ^ 2 := by
        apply Finset.sum_le_sum
        intro γ hγ
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        have h_anchoredVectorMoment_coordinate_bound : |anchoredVectorMoment u p g γ| ≤ b * F := by
          let := cubeVolume_isProbability d
          have hbound : ∀ᵐ w ∂cubeVolume d,
              ‖p w * anchoredFeature u w γ * g w‖ ≤ b * F := by
            filter_upwards [hp, ae_restrict_mem (show MeasurableSet (unitCube d) from
              (unitCube_isCompact d).isClosed.measurableSet)] with w hw hcube
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw.1]
            have h_anchoredFeature_abs_le_one : |anchoredFeature u w γ| ≤ 1 := by
              apply anchoredMonomial_abs_le_one
              intro i
              change |w i - u i| ≤ 1
              rw [abs_le]
              constructor <;> linarith [(hu i).1, (hu i).2, (hcube i).1, (hcube i).2]
            have hφ := h_anchoredFeature_abs_le_one
            have hφ0 := abs_nonneg (anchoredFeature u w γ)
            have hg0 := abs_nonneg (g w)
            calc
              p w * |anchoredFeature u w γ| * |g w| ≤ b * 1 * F :=
                mul_le_mul (mul_le_mul hw.2 hφ hφ0 hb) (hg w hcube) hg0 (mul_nonneg hb (by norm_num))
              _ = b * F := by ring
          simpa only [Real.norm_eq_abs, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, anchoredVectorMoment]
            using norm_integral_le_of_norm_le_const hbound
        exact h_anchoredVectorMoment_coordinate_bound
      _ = (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (b * F) ^ 2 := by simp
      _ = (Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (b * F)) ^ 2 := by
        simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
theorem anchoredGram_inverse_uniform_bound  :
    ∃ N : ℝ, 0 < N ∧ ∀ u ∈ unitCube d, ‖(anchoredGram (ℓ := ℓ) u)⁻¹‖ ≤ N := by
  have hc : Continuous (fun u : Covariate d => (anchoredGram (ℓ := ℓ) u)⁻¹) := by
    have heq : (fun u : Covariate d => (anchoredGram (ℓ := ℓ) u)⁻¹) =
        fun u => anchoredWhitening u * anchoredWhitening u :=
      funext anchoredWhitening_square
    rw [heq]
    exact (anchoredWhitening_continuous (d := d) (ℓ := ℓ)).mul anchoredWhitening_continuous
  obtain ⟨M, hM⟩ := (unitCube_isCompact d).bddAbove_image hc.norm.continuousOn
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro u hu
  exact (hM (mem_image_of_mem _ hu)).trans (le_max_right _ _)
section Reindex
variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    [Nonempty n] [Nonempty m]
theorem reindex_matrix_norm (e : n ≃ m) (A : Matrix n n ℝ) : ‖A.reindex e e‖ = ‖A‖ := by
  let φ := Matrix.reindexAlgEquiv ℝ ℝ e
  change ‖φ A‖ = ‖A‖
  have hs : IsSelfAdjoint (star A * A) := .star_mul_self A
  have hs' : IsSelfAdjoint (φ (star A * A)) := Matrix.isHermitian_iff_isSelfAdjoint.mp
    ((Matrix.isHermitian_iff_isSelfAdjoint.mpr hs).reindex e)
  have hgS := IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (φ (star A * A)) hs'
  rw [AlgEquiv.spectrum_eq φ _] at hgS
  have he : ‖φ (star A * A)‖ = ‖star A * A‖ := hgS.unique (IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum (𝕜 := ℝ) (star A * A) hs)
  have hm : φ (star A * A) = star (φ A) * φ A := by
    rw [map_mul]
    rfl
  rw [hm, CStarRing.norm_star_mul_self, CStarRing.norm_star_mul_self] at he
  exact (mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)).mp he
end Reindex
abbrev anchoredDimension (d ℓ : ℕ) := Fintype.card (AnchoredIndex d ℓ)
instance anchoredDimension_neZero {d ℓ : ℕ} [Nonempty (AnchoredIndex d ℓ)] :
    NeZero (anchoredDimension d ℓ) := ⟨Fintype.card_ne_zero⟩
def anchoredFinReindex (d ℓ ) : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ ≃ₐ[ℝ]
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  Matrix.reindexAlgEquiv ℝ ℝ (Fintype.equivFin (AnchoredIndex d ℓ))
def anchoredFinNormalizedGram  (u : Covariate d) (p : Covariate d → ℝ) :
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  anchoredFinReindex d ℓ ((anchoredGram u)⁻¹ * anchoredDensityGram u p)
def anchoredFinSimilarityUnit  (u : Covariate d) :
    (Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ)ˣ :=
  Units.map (anchoredFinReindex d ℓ).toMonoidHom (anchoredSimilarityUnit u)
theorem anchoredFin_similarity  (u p) :
    matrixSimilarity (anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹ (anchoredFinNormalizedGram u p) =
      anchoredFinReindex d ℓ (anchoredWhitenedGram u p) := by
  change anchoredFinReindex d ℓ _ * anchoredFinReindex d ℓ _ * anchoredFinReindex d ℓ _ = _
  rw [← map_mul, ← map_mul]
  have h_anchored_preconditioned_similarity : ((anchoredSimilarityUnit (ℓ := ℓ) u)⁻¹).val *
      ((anchoredGram u)⁻¹ * anchoredDensityGram u p) *
      (anchoredSimilarityUnit (ℓ := ℓ) u).val = anchoredWhitenedGram u p := by
    rw [anchoredSimilarityUnit_val, anchoredSimilarityUnit_inv_val, (anchoredWhitening_square (ℓ := ℓ) u)]
    simp only [← Matrix.mul_assoc, anchoredWhitenedGram]
    rw [show CFC.sqrt (anchoredGram u) * anchoredWhitening u = 1 by
      exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)), one_mul]
  exact congrArg (anchoredFinReindex d ℓ) h_anchored_preconditioned_similarity
theorem anchoredFin_similarity_isHermitian  (u : Covariate d) (p : Covariate d → ℝ) :
    (matrixSimilarity (anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹ (anchoredFinNormalizedGram u p)).IsHermitian := by
  rw [anchoredFin_similarity]
  exact (anchoredWhitenedGram_isHermitian u p).reindex (Fintype.equivFin (AnchoredIndex d ℓ))
theorem anchoredFin_similarity_spectrum  (u p) (hpmeas : Measurable p) (a b ) (ha : 0 ≤ a)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) :
    spectrum ℝ (matrixSimilarity (anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹ (anchoredFinNormalizedGram u p)) ⊆ Set.Icc a b := by
  rw [anchoredFin_similarity, AlgEquiv.spectrum_eq]
  have h_anchoredWhitening_gram_identity (u : Covariate d) : anchoredWhitening (ℓ := ℓ) u * anchoredGram u * anchoredWhitening u = 1 := by
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp (anchoredGram_sqrt_isUnit (ℓ := ℓ) u)
    calc
      _ = anchoredWhitening u *
          (CFC.sqrt (anchoredGram u) * CFC.sqrt (anchoredGram u)) * anchoredWhitening u :=
        congrArg (fun M => anchoredWhitening u * M * anchoredWhitening u)
          (CFC.sqrt_mul_sqrt_self (anchoredGram u) (anchoredGram_posDef u).posSemidef.nonneg).symm
      _ = 1 := by
        unfold anchoredWhitening
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, one_mul,
          Matrix.mul_nonsing_inv _ hdet]
  have h_anchoredWhitenedGram_sandwich : a • (1 : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) ≤ anchoredWhitenedGram u p ∧
      anchoredWhitenedGram u p ≤ b • (1 : Matrix (AnchoredIndex d ℓ) (AnchoredIndex d ℓ) ℝ) := by
    have h_anchoredDensityGram_sandwich : (anchoredDensityGram (ℓ := ℓ) u p - a • anchoredGram u).PosSemidef ∧
      (b • anchoredGram u - anchoredDensityGram (ℓ := ℓ) u p).PosSemidef := by
      constructor
      · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
          ((anchoredDensityGram_isHermitian u p).sub
            ((anchoredGram_isHermitian u).smul (by simp [IsSelfAdjoint])))
        intro c
        simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
        exact sub_nonneg.mpr (anchoredDensityGram_quadratic_bounds u p hpmeas a b ha hp c).1
      · apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
          (((anchoredGram_isHermitian u).smul (by simp [IsSelfAdjoint])).sub
            (anchoredDensityGram_isHermitian u p))
        intro c
        simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul]
        exact sub_nonneg.mpr (anchoredDensityGram_quadratic_bounds u p hpmeas a b ha hp c).2
    have h := h_anchoredDensityGram_sandwich
    constructor
    · have hlo := h.1.conjTranspose_mul_mul_same (anchoredWhitening u)
      rw [(anchoredWhitening_isHermitian u).eq] at hlo
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        h_anchoredWhitening_gram_identity] at hlo
      exact hlo
    · have hup := h.2.conjTranspose_mul_mul_same (anchoredWhitening u)
      rw [(anchoredWhitening_isHermitian u).eq] at hup
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
        h_anchoredWhitening_gram_identity] at hup
      exact hup
  have hs := h_anchoredWhitenedGram_sandwich
  intro t ht
  exact ⟨(algebraMap_le_iff_le_spectrum (anchoredWhitenedGram_isHermitian u p)).mp (by simpa only [Algebra.algebraMap_eq_smul_one] using hs.1) t ht,
    (le_algebraMap_iff_spectrum_le (anchoredWhitenedGram_isHermitian u p)).mp (by simpa only [Algebra.algebraMap_eq_smul_one] using hs.2) t ht⟩
theorem anchoredFinSimilarityUnit_uniform_condition  [Nonempty (AnchoredIndex d ℓ)] :
    ∃ χ, 0 < χ ∧ ∀ u ∈ unitCube d,
      ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ *
        ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ := by
  have h_anchoredSimilarityUnit_uniform_condition : ∃ χ, 0 < χ ∧ ∀ u ∈ unitCube d,
      ‖(anchoredSimilarityUnit (ℓ := ℓ) u).val‖ *
        ‖((anchoredSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ := by
    have hc  :=
      (anchoredWhitening_continuous (d := d) (ℓ := ℓ)).norm.mul
        (anchoredGram_sqrt_continuous (d := d) (ℓ := ℓ)).norm
    obtain ⟨M, hM⟩ := (unitCube_isCompact d).bddAbove_image hc.continuousOn
    refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro u hu
    rw [anchoredSimilarityUnit_val, anchoredSimilarityUnit_inv_val]
    exact (hM (Set.mem_image_of_mem _ hu)).trans (le_max_right _ _)
  obtain ⟨χ, hχ, hQ⟩ := h_anchoredSimilarityUnit_uniform_condition
  refine ⟨χ, hχ, ?_⟩
  intro u hu
  have h_anchoredFinSimilarityUnit_val (u : Covariate d) : (anchoredFinSimilarityUnit (ℓ := ℓ) u).val = anchoredFinReindex d ℓ (anchoredSimilarityUnit u).val := rfl
  have h_anchoredFinSimilarityUnit_inv_val (u : Covariate d) : ((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val =
      anchoredFinReindex d ℓ ((anchoredSimilarityUnit u)⁻¹).val := rfl
  rw [h_anchoredFinSimilarityUnit_val, h_anchoredFinSimilarityUnit_inv_val]
  change ‖((anchoredSimilarityUnit u).val).reindex _ _‖ *
    ‖(((anchoredSimilarityUnit u)⁻¹).val).reindex _ _‖ ≤ χ
  rw [reindex_matrix_norm, reindex_matrix_norm]
  exact hQ u hu
theorem anchoredFinNormalizedGram_norm_le  [Nonempty (AnchoredIndex d ℓ)]
    (u : Covariate d) (p : Covariate d → ℝ) (hpmeas : Measurable p)
    (a b χ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hχ : 0 ≤ χ)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hQ : ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ *
      ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ) :
    ‖anchoredFinNormalizedGram (ℓ := ℓ) u p‖ ≤ χ * b := by
  let Q := anchoredFinSimilarityUnit (ℓ := ℓ) u
  let A := anchoredFinNormalizedGram (ℓ := ℓ) u p
  have he : matrixSimilarity Q (matrixSimilarity Q⁻¹ A) = A := by
    simp [matrixSimilarity, Matrix.mul_assoc]
  change ‖A‖ ≤ χ * b
  rw [← he]
  apply (matrixSimilarity_norm_le Q _).trans
  have h_positive_spectral_matrix_norm_le {n} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ) (hA : A.IsHermitian) (hSpec : spectrum ℝ A ⊆ Set.Icc a b) : ‖A‖ ≤ b := by
    rw [← cfc_id ℝ A (Matrix.isHermitian_iff_isSelfAdjoint.mp hA)]
    apply norm_cfc_le hb
    intro t ht
    rw [id_eq, Real.norm_eq_abs, abs_of_nonneg (ha.trans (hSpec ht).1)]
    exact (hSpec ht).2
  exact mul_le_mul hQ
    (h_positive_spectral_matrix_norm_le _ (anchoredFin_similarity_isHermitian u p) (anchoredFin_similarity_spectrum u p hpmeas a b ha hp)) (norm_nonneg _) hχ
theorem matrix_real_entry_norm_le  [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℝ) (i j ) : ‖A i j‖ ≤ ‖A‖ := by
  rw [← complexify_matrix_norm A, ← Complex.norm_real (A i j)]
  exact matrix_entry_norm_le_l2 (A.map Complex.ofReal) i j
theorem incrementValuation_norm_le {r : ℕ} [NeZero r]
    (A C ) (U V : Bool → Fin r → ℝ)
    (M W ) (hM : 0 ≤ M) (hW : 0 ≤ W)
    (hA : ‖A‖ ≤ M) (hC : ‖C‖ ≤ M) (hU : ∀ t, ‖U t‖ ≤ W) (hV : ∀ t, ‖V t‖ ≤ W) :
    ‖incrementValuation A C U V‖ ≤ max M W := by
  apply (pi_norm_le_iff_of_nonneg (hM.trans (le_max_left _ _))).mpr
  intro z
  cases z with
  | inl z =>
    cases z with
    | inl ij => exact ((matrix_real_entry_norm_le A ij.1 ij.2).trans hA).trans (le_max_left _ _)
    | inr z => exact ((matrix_real_entry_norm_le C z.2.1 z.2.2).trans hC).trans (le_max_left _ _)
  | inr z =>
    rcases z with ⟨parent, response, i⟩
    cases parent with
    | false => exact ((norm_le_pi_norm (U response) i).trans (hU response)).trans (le_max_right _ _)
    | true => exact ((norm_le_pi_norm (V response) i).trans (hV response)).trans (le_max_right _ _)
def populationInverseDerivativeCenter  [Nonempty (AnchoredIndex d ℓ)]
    (u v : Covariate d) (p q : Covariate d → ℝ) (hpmeas : Measurable p) (hqmeas : Measurable q)
    (a b χ W : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hχ : 0 ≤ χ) (hW : 0 ≤ W)
    (hp : ∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b)
    (hq : ∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b)
    (hUQ : ‖(anchoredFinSimilarityUnit (ℓ := ℓ) u).val‖ * ‖((anchoredFinSimilarityUnit (ℓ := ℓ) u)⁻¹).val‖ ≤ χ)
    (hVQ : ‖(anchoredFinSimilarityUnit (ℓ := ℓ) v).val‖ * ‖((anchoredFinSimilarityUnit (ℓ := ℓ) v)⁻¹).val‖ ≤ χ)
    (U V : Bool → Fin (anchoredDimension d ℓ) → ℝ)
    (hU : ∀ t, ‖U t‖ ≤ W) (hV : ∀ t, ‖V t‖ ≤ W) :
    InverseDerivativeCenter (anchoredDimension d ℓ) a b χ (max (χ * b) W) where
  moments := incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V
  normBound := incrementValuation_norm_le _ _ U V _ W (mul_nonneg hχ hb) hW
    (anchoredFinNormalizedGram_norm_le u p hpmeas a b χ ha hb hχ hp hUQ)
    (anchoredFinNormalizedGram_norm_le v q hqmeas a b χ ha hb hχ hq hVQ) hU hV
  currentChart := anchoredFinSimilarityUnit u
  parentChart := anchoredFinSimilarityUnit v
  currentCondition := hUQ
  parentCondition := hVQ
  currentHermitian := anchoredFin_similarity_isHermitian u p
  parentHermitian := anchoredFin_similarity_isHermitian v q
  currentSpectrum := anchoredFin_similarity_spectrum u p hpmeas a b ha hp
  parentSpectrum := anchoredFin_similarity_spectrum v q hqmeas a b ha hq
def anchoredFinTransport (d ℓ ) :
    Matrix (Fin (anchoredDimension d ℓ)) (Fin (anchoredDimension d ℓ)) ℝ :=
  anchoredFinReindex d ℓ (anchoredTransport d ℓ)
theorem anchored_population_inverse_derivatives  [Nonempty (AnchoredIndex d ℓ)]
    (a b W Y ) (ha : 0 < a) (hab : a < b) (hW : 0 ≤ W) (hY : 0 ≤ Y) :
    ∃ C A, 0 < C ∧ 0 < A ∧
      ∀ u v, u ∈ unitCube d → v ∈ unitCube d →
      ∀ p q, Measurable p → Measurable q →
      (∀ᵐ w ∂cubeVolume d, a ≤ p w ∧ p w ≤ b) →
      (∀ᵐ w ∂cubeVolume d, a ≤ q w ∧ q w ≤ b) →
      ∀ (U V : Bool → Fin (anchoredDimension d ℓ) → ℝ),
      (∀ t, ‖U t‖ ≤ W) → (∀ t, ‖V t‖ ≤ W) →
      ∀ y, |y| ≤ Y → ∀ m k directions,
        ‖iteratedFDeriv ℝ k (incrementFinVector (anchoredDimension d ℓ) a b (anchoredFinTransport d ℓ) y m)
          (fun j => incrementValuation (anchoredFinNormalizedGram u p) (anchoredFinNormalizedGram v q) U V
            ((Fintype.equivFin (incrementVariables (anchoredDimension d ℓ))).symm j)) directions‖ ≤
            C * k.factorial * A ^ k * ∏ j, ‖directions j‖ := by
  obtain ⟨χ, hχ, hQ⟩ := anchoredFinSimilarityUnit_uniform_condition (d := d) (ℓ := ℓ)
  let η := (1 + RoughRegime.Upper.intervalRho a b) / 2
  have := RoughRegime.Upper.intervalRho_lt_one a b ha hab
  have hρη : RoughRegime.Upper.intervalRho a b < η := by dsimp [η]; linarith
  have hη1 : η < 1 := by dsimp [η]; linarith
  have hη  := (RoughRegime.Upper.intervalRho_pos a b ha hab).trans hρη
  let L := max (χ * b) W
  have hb  := ha.trans hab
  let M := similarIncrementEnvelope (anchoredDimension d ℓ) a b
    (RoughRegime.Upper.intervalRho a b / η) χ L Y (anchoredFinTransport d ℓ)
  refine ⟨max 1 M, inverseDerivativeRate (anchoredDimension d ℓ) a b η χ,
    (zero_lt_one : (0 : ℝ) < 1).trans_le (le_max_left _ _),
    inverseDerivativeRate_pos _ a b η χ hη hη1 hχ, ?_⟩
  intro u v hu hv p q hpmeas hqmeas hp hq U V hU hV y hy m k directions
  let c : InverseDerivativeCenter (anchoredDimension d ℓ) a b χ L :=
    populationInverseDerivativeCenter (ℓ := ℓ) u v p q hpmeas hqmeas a b χ W ha.le hb.le hχ.le hW
    hp hq (hQ u hu) (hQ v hv) U V hU hV
  have h := paper_inverse_vector_derivative_bound (anchoredDimension d ℓ) a b ha hab η hρη hη1 χ hχ
    L Y ((mul_nonneg hχ.le hb.le).trans (le_max_left _ _)) hY (anchoredFinTransport d ℓ) y hy c m k directions
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg (fun j _ => norm_nonneg (directions j)))
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (inverseDerivativeRate_pos (anchoredDimension d ℓ) a b η χ hη hη1 hχ).le k)
  exact mul_le_mul_of_nonneg_right (le_max_right 1 M) (Nat.cast_nonneg _)
def anchoredFinMomentFamilies  (u : Covariate d)
    (p f : Covariate d → ℝ) : Bool → Fin (anchoredDimension d ℓ) → ℝ :=
  fun t i => anchoredPreconditionedMoment u p (if t then fun _ => 1 else f)
    ((Fintype.equivFin (AnchoredIndex d ℓ)).symm i)
theorem anchoredFinMomentFamilies_uniform_bound 
    (b F ) (hb : 0 ≤ b) (hF : 0 ≤ F) :
    ∃ W, 0 < W ∧ ∀ u ∈ unitCube d, ∀ p f,
      (∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) →
      (∀ w ∈ unitCube d, |f w| ≤ F) →
      ∀ t, ‖anchoredFinMomentFamilies (ℓ := ℓ) u p f t‖ ≤ W := by
  have h_anchoredPreconditionedMoment_uniform_bound : ∃ W, 0 < W ∧ ∀ u ∈ unitCube d, ∀ p g,
      (∀ᵐ w ∂cubeVolume d, 0 ≤ p w ∧ p w ≤ b) →
      (∀ w ∈ unitCube d, |g w| ≤ max 1 F) →
      ‖anchoredPreconditionedMoment (ℓ := ℓ) u p g‖ ≤ W := by
    have hF : 0 ≤ (max 1 F) := le_trans zero_le_one (le_max_left _ _)
    obtain ⟨N, hN, hNu⟩ := anchoredGram_inverse_uniform_bound (d := d) (ℓ := ℓ)
    let W := max 1 (N * (Real.sqrt (Fintype.card (AnchoredIndex d ℓ) : ℝ) * (b * max 1 F)))
    refine ⟨W, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro u hu p g hp hg
    have hA := Matrix.l2_opNorm_mulVec ((anchoredGram (ℓ := ℓ) u)⁻¹)
      ((EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm (anchoredVectorMoment u p g))
    have hpre : ‖(EuclideanSpace.equiv (AnchoredIndex d ℓ) ℝ).symm
        (anchoredPreconditionedMoment u p g)‖ ≤ W := by
      apply hA.trans
      apply (mul_le_mul (hNu u hu) (anchoredVectorMoment_norm_bound (ℓ := ℓ) u hu p g b (max 1 F) hb hF hp hg) (norm_nonneg _) hN.le).trans
      exact le_max_right _ _
    apply (pi_norm_le_iff_of_nonneg (by dsimp [W]; positivity)).mpr
    intro γ
    exact (PiLp.norm_apply_le _ γ).trans hpre
  obtain ⟨W, hW, hm⟩ := h_anchoredPreconditionedMoment_uniform_bound
  refine ⟨W, hW, ?_⟩
  intro u hu p f hp hf t
  have hg : ∀ w ∈ unitCube d, |(if t then fun _ => 1 else f) w| ≤ max 1 F := by
    intro w hw
    cases t
    · exact (hf w hw).trans (le_max_right _ _)
    · simp
  apply (pi_norm_le_iff_of_nonneg hW.le).mpr
  intro i
  exact (norm_le_pi_norm _ ((Fintype.equivFin (AnchoredIndex d ℓ)).symm i)).trans (hm u hu p _ hp hg)
end NearlyMinimax
