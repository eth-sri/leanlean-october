module
import Mathlib
public import OAI.NumberTheory.DirichletL.Descent.IdealMasks
public import OAI.NumberTheory.DirichletL.Descent.Fibers
public import OAI.NumberTheory.DirichletL.CubicSieve.Ideal

@[expose] public section

namespace OAI

namespace SevenEighths.InverseMoment

noncomputable section

open scoped BigOperators Classical
open ActualEisensteinCubic

open scoped EisensteinEis

def inverseCubicKernel (P n : Ideal Eis) : ℂ :=
  star (ConcreteTraceCRT.eisEmbedding
    (CubicJacobiGlobal.idealSymbol P (CompletedGauss.primaryGenerator n)))

theorem inverseCubicKernel_eq_inverse_square (P n : Ideal Eis) :
    inverseCubicKernel P n =
      (CanonicalRowCompletion.idealRowHom (CompletedGauss.primaryGenerator n) P)⁻¹ ^ 2 := by
  rw [inv_pow, CanonicalRowCompletion.idealRowHom_square,
    inverse_eq_square_of_fourth_eq (CubicSieve.idealSymbol_fourth P _)]
  exact (CubicSieve.idealKernel_square_eq_star P n).symm

theorem inverseCubicKernel_norm_le_one (P n : Ideal Eis) :
    ‖inverseCubicKernel P n‖ ≤ 1 := by
  simpa only [inverseCubicKernel, norm_star, CubicSieve.idealKernel] using
    CubicSieve.idealKernel_norm_le_one P n

def hybridCubicCoefficient (R r h t : Ideal Eis) (a : Ideal Eis → ℂ)
    (P : Ideal Eis) : ℂ :=
  (a (R * P) * inverseCubicKernel P r * (if IsCoprime P (h * t) then 1 else 0)) /
    (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)

theorem dyadic_normalized_coefficient_energy
    (S : Finset (Ideal Eis)) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ P ∈ S, ‖a P‖ ≤ 1) :
    (∑ P ∈ S, ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2) ≤ 256 := by
  have hL0 : 0 < L := by linarith
  have hP0 (P : Ideal Eis) (hP : P ∈ S) : 0 < (Ideal.absNorm P : ℝ) :=
    hL0.trans_le (hS P hP).1
  have hcount : (S.card : ℝ) ≤ 128 * (2 * L) := by
    apply DescentFiberCost.finite_ideal_count_real S (2 * L) (by linarith)
    · intro P hP hz
      have hn := hP0 P hP
      simp [hz] at hn
    · intro P hP
      exact (hS P hP).2
  have hterm (P : Ideal Eis) (hP : P ∈ S) :
      ‖a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)‖ ^ 2 ≤ 1 / L := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    calc
      _ ≤ 1 / (Ideal.absNorm P : ℝ) :=
        div_le_div_of_nonneg_right
          (by simpa using pow_le_pow_left₀ (norm_nonneg _) (ha P hP) 2) (hP0 P hP).le
      _ ≤ _ := one_div_le_one_div_of_le hL0 (hS P hP).1
  calc
    _ ≤ ∑ _P ∈ S, (1 / L : ℝ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) / L := by simp [div_eq_mul_inv]
    _ ≤ (128 * (2 * L)) / L := div_le_div_of_nonneg_right hcount hL0.le
    _ = 256 := by field_simp; ring

theorem hybridCubicCoefficient_energy
    (R r h t : Ideal Eis) (S : Finset (Ideal Eis)) (L : ℝ) (hL : 1 ≤ L)
    (hS : ∀ P ∈ S, L ≤ (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ 2 * L)
    (a : Ideal Eis → ℂ) (ha : ∀ P ∈ S, ‖a (R * P)‖ ≤ 1) :
    (∑ P ∈ S, ‖hybridCubicCoefficient R r h t a P‖ ^ 2) ≤ 256 := by
  apply dyadic_normalized_coefficient_energy S L hL hS
  intro P hP
  by_cases hc : IsCoprime P (h * t)
  · simp only [hc, ite_eq_left, mul_one, norm_mul]
    exact (mul_le_mul (ha P hP) (inverseCubicKernel_norm_le_one P r)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  · simp [hc]

theorem inverseCubicKernel_mul_left (R P n : Ideal Eis) :
    inverseCubicKernel (R * P) n = inverseCubicKernel R n * inverseCubicKernel P n := by
  simp only [inverseCubicKernel, CubicJacobiGlobal.idealSymbol_mul, map_mul, star_mul]
  ring

theorem inverseCubicKernel_mul_right (P n m : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0) :
    inverseCubicKernel P (n * m) = inverseCubicKernel P n * inverseCubicKernel P m := by
  change star (CubicSieve.idealNumeratorHom P hP (n * m)) =
    star (CubicSieve.idealNumeratorHom P hP n) * star (CubicSieve.idealNumeratorHom P hP m)
  simp

theorem inverseCubicKernel_quotients (R P' r c' m : Ideal Eis)
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0) :
    inverseCubicKernel (R * P') ((r * c') * m) =
      inverseCubicKernel R ((r * c') * m) * inverseCubicKernel P' r *
        inverseCubicKernel P' (c' * m) := by
  rw [inverseCubicKernel_mul_left, mul_assoc r c' m,
    inverseCubicKernel_mul_right P' r (c' * m) hP']
  ring

theorem inverseCubicKernel_eq_zero_of_not_coprime (P n : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hn : CompletedGauss.primaryGenerator n ≠ 0) (hcop : ¬ IsCoprime P n) :
    inverseCubicKernel P n = 0 := by
  have hc := CubicSieve.idealSymbol_cube_mask P (CompletedGauss.primaryGenerator n) hP
  rw [(CompletedGauss.primaryGenerator_spec n hn).1, ite_eq_right hcop] at hc
  have hz := (pow_eq_zero_iff (by decide : (3 : ℕ) ≠ 0)).mp hc
  simp only [inverseCubicKernel, hz, star_zero]

theorem hybrid_cubic_column_mask
    (P n b c m h t : Ideal Eis)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hngen : CompletedGauss.primaryGenerator n ≠ 0)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2) :
    inverseCubicKernel P n * (if IsCoprime P b then 1 else 0) =
      inverseCubicKernel P n * (if IsCoprime P (h * t) then 1 else 0) := by
  by_cases hc : IsCoprime P c
  · have he : IsCoprime P b ↔ IsCoprime P (h * t) := by
      rw [hb]
      simp only [IsCoprime.mul_right_iff, IsCoprime.pow_right_iff (by decide : 0 < 2),
        hc, true_and]
    simp only [he]
  · have hPn : ¬ IsCoprime P n := by
      rw [hn, IsCoprime.mul_right_iff]
      exact fun hcop => hc hcop.1
    rw [inverseCubicKernel_eq_zero_of_not_coprime P n hP hngen hPn]
    simp

theorem hybrid_original_kernel_decomposition
    (k P n b c m h t : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible k)
    (hP : CompletedGauss.primaryGenerator P ≠ 0)
    (hngen : CompletedGauss.primaryGenerator n ≠ 0)
    (hn : n = c * m) (hb : b = (c * h) * t ^ 2)
    (hct : CompletedGauss.primaryGenerator (c * t) ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (n * b)) *
      inverseCubicKernel P n * (if IsCoprime P b then 1 else 0) *
      (if IsCoprime k P then 1 else 0) =
    (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) *
      CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel P n * (if IsCoprime P (h * t) then 1 else 0) := by
  have hm : ((if IsCoprime k P then (1 : ℂ) else 0) *
      (if IsCoprime k (c * t) then 1 else 0)) =
      (if IsCoprime k t then 1 else 0) * (if IsCoprime k (P * c) then 1 else 0) := by
    simp only [IsCoprime.mul_right_iff]
    by_cases hkp : IsCoprime k P <;> by_cases hkc : IsCoprime k c <;>
      by_cases hkt : IsCoprime k t <;> simp [hkp, hkc, hkt]
  calc
    _ = ((if IsCoprime k P then 1 else 0) * (if IsCoprime k (c * t) then 1 else 0)) *
        CanonicalQuadraticSieve.quadraticRow k (CompletedGauss.primaryGenerator (m * h)) *
        (inverseCubicKernel P n * (if IsCoprime P b then 1 else 0)) := by
      rw [hybrid_quadratic_square_mask k n b c m h t hk hn hb hct]
      ring
    _ = _ := by rw [hm, hybrid_cubic_column_mask P n b c m h t hP hngen hn hb]; ring

theorem hybrid_kernel_quotients (R r k' P' c' m h : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible ((R * r) * k'))
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0) :
    CanonicalQuadraticSieve.quadraticRow ((R * r) * k')
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel (R * P') ((r * c') * m) =
    (CanonicalQuadraticSieve.quadraticRow (R * r)
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel R ((r * c') * m)) *
      inverseCubicKernel P' r *
      CanonicalQuadraticSieve.quadraticRow k'
        (CompletedGauss.primaryGenerator (m * h)) *
      inverseCubicKernel P' (c' * m) := by
  rw [CanonicalQuadraticSieve.quadraticRow_mul (R * r) k' hk,
    inverseCubicKernel_quotients R P' r c' m hP']
  ring

def hybridColumnCoefficient (R r : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (c m h : Ideal Eis) : ℂ :=
  beta (r * c) m h *
    CanonicalQuadraticSieve.quadraticRow (R * r) (CompletedGauss.primaryGenerator (m * h)) *
    inverseCubicKernel R ((r * c) * m)

theorem hybridColumnCoefficient_norm_le_one (R r c m h : Ideal Eis)
    (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) (hb : ‖beta (r * c) m h‖ ≤ 1) :
    ‖hybridColumnCoefficient R r beta c m h‖ ≤ 1 := by
  simp only [hybridColumnCoefficient, norm_mul]
  have hfirst : ‖beta (r * c) m h‖ *
      ‖CanonicalQuadraticSieve.quadraticRow (R * r)
        (CompletedGauss.primaryGenerator (m * h))‖ ≤ 1 := by
    exact (mul_le_mul hb (CanonicalQuadraticSieve.quadraticRow_norm_le_one _ _)
      (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
  exact (mul_le_mul hfirst (inverseCubicKernel_norm_le_one R ((r * c) * m))
    (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

theorem normalized_ideal_product_weight (R P : Ideal Eis) (z : ℂ) :
    z / (Real.sqrt (Ideal.absNorm (R * P) : ℝ) : ℂ) =
      (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
        (z / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)) := by
  rw [map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  ring

theorem hybrid_extracted_block_identity
    (R r k' P' c m h t : Ideal Eis)
    (hk : CanonicalQuadraticSieve.Admissible ((R * r) * k'))
    (hP' : CompletedGauss.primaryGenerator P' ≠ 0)
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → Ideal Eis → ℂ) :
    a (R * P') / (Real.sqrt (Ideal.absNorm (R * P') : ℝ) : ℂ) *
      beta (r * c) m h *
      (CanonicalQuadraticSieve.quadraticRow ((R * r) * k')
          (CompletedGauss.primaryGenerator (m * h)) *
        inverseCubicKernel (R * P') ((r * c) * m)) *
      (if IsCoprime P' (h * t) then 1 else 0) =
    (Real.sqrt (Ideal.absNorm R : ℝ) : ℂ)⁻¹ *
      hybridColumnCoefficient R r beta c m h *
      CanonicalQuadraticSieve.quadraticRow k' (CompletedGauss.primaryGenerator (m * h)) *
      hybridCubicCoefficient R r h t a P' * inverseCubicKernel P' (c * m) := by
  rw [normalized_ideal_product_weight, hybrid_kernel_quotients R r k' P' c m h hk hP']
  simp only [hybridColumnCoefficient, hybridCubicCoefficient, div_eq_mul_inv]
  ring

def hybridInner (nset bset : Finset (Ideal Eis))
    (beta : Ideal Eis → Ideal Eis → ℂ) (k P : Ideal Eis) : ℂ :=
  ∑ n ∈ nset, ∑ b ∈ bset,
    beta n b * CanonicalQuadraticSieve.quadraticRow k
      (CompletedGauss.primaryGenerator (n * b)) * inverseCubicKernel P n *
        (if IsCoprime P b then 1 else 0)

def hybridRow (Pset nset bset : Finset (Ideal Eis))
    (a : Ideal Eis → ℂ) (beta : Ideal Eis → Ideal Eis → ℂ) (k : Ideal Eis) : ℂ :=
  ∑ P ∈ Pset, a P / (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ) *
    (if IsCoprime k P then 1 else 0) * hybridInner nset bset beta k P






