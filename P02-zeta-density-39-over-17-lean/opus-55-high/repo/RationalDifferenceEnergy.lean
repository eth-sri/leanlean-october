module
public import RationalGcdDecomposition
public import Mathlib
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-! An unconditional finite Gram identity and its coefficient bound.
These apply to the actual phase kernel in the difference-sum argument. -/
set_option autoImplicit false
noncomputable section
open Finset

namespace Montgomery.RationalMoment
variable {ι τ : Type*}

section
variable (A : Finset ι)
include A
theorem square_sum_expansion (f : ι → ℂ) :
    ((‖∑ n ∈ A, f n‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ A, ∑ m ∈ A, f n * star (f m) := by
  have hh := Complex.mul_conj' (∑ n ∈ A, f n)
  rw [starRingEnd_apply, ← Complex.ofReal_pow] at hh
  rw [← hh]
  pm_210 star_sum sum_mul mul_sum sum_comm

theorem gram_energy_identity (W : Finset τ)
    (K : ι → τ → ℂ) (a : ι → ℂ) :
    ((∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * K n t * star (K n u)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ A, ∑ m ∈ A, (a n * star (a m)) *
        ((‖∑ t ∈ W, K n t * star (K m t)‖ ^ 2 : ℝ) : ℂ) := by
  simp only [Complex.ofReal_sum, square_sum_expansion, mul_sum]
  calc
    _ = ∑ t ∈ W, ∑ n ∈ A, ∑ u ∈ W, ∑ m ∈ A,
        (a n * K n t * star (K n u)) * star (a m * K m t * star (K m u)) := by
      apply sum_congr rfl
      intro t _
      rw [sum_comm]
    _ = ∑ n ∈ A, ∑ t ∈ W, ∑ m ∈ A, ∑ u ∈ W,
        (a n * K n t * star (K n u)) * star (a m * K m t * star (K m u)) := by
      rw [sum_comm]
      pm_156 sum_congr n t
      rw [sum_comm]
    _ = _ := by
      pm_150 sum_congr n sum_comm m
      pm_156 sum_congr t u
      simp only [star_mul, star_star]
      ring

/-- Coefficients of modulus at most one cannot increase this difference
energy beyond the corresponding sum over all ordered frequency pairs. -/
theorem gram_energy_le (W : Finset τ)
    (K : ι → τ → ℂ) (a : ι → ℂ) (ha : ∀ n ∈ A, ‖a n‖ ≤ 1) :
    (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * K n t * star (K n u)‖ ^ 2) ≤
      ∑ n ∈ A, ∑ m ∈ A, ‖∑ t ∈ W, K n t * star (K m t)‖ ^ 2 := by
  let E : ℝ := ∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * K n t * star (K n u)‖ ^ 2
  have hE : 0 ≤ E := sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sq_nonneg _))
  have he : E = ‖(E : ℂ)‖ := by simp [Real.norm_eq_abs, abs_of_nonneg hE]
  change E ≤ _
  rw [he, show (E : ℂ) = _ from gram_energy_identity A W K a]
  pm_244 sum_le_sum n hn
  pm_244 sum_le_sum m hm
  rw [norm_mul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  have hab : ‖a n‖ * ‖a m‖ ≤ 1 := by
    nlinarith [ha n hn, ha m hm, norm_nonneg (a n), norm_nonneg (a m),
      mul_nonneg (sub_nonneg.mpr (ha n hn)) (sub_nonneg.mpr (ha m hm))]
  pm_5506 hab
end

theorem phase_time_difference (r t u : ℝ) :
    phase r t * star (phase r u) = phase r (t - u) := by
  change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_frequency_ratio {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (t : ℝ) :
    phase r t * star (phase s t) = phase (r / s) t := by
  change Complex.exp _ * (starRingEnd ℂ) (Complex.exp _) = Complex.exp _
  rw [← Complex.exp_conj]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [← Complex.exp_add, Real.log_div hr.ne' hs.ne']
  congr 1
  push_cast
  ring

/-- The literal Dirichlet difference sum is bounded by the all-pairs rational
second moment. No moment, separation, or density estimate is assumed. -/
theorem dirichlet_difference_energy_le (A : Finset ℕ)
    (hA : ∀ n ∈ A, 0 < n) (W : Finset ℝ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ A, ‖a n‖ ≤ 1) :
    (∑ t ∈ W, ∑ u ∈ W, ‖∑ n ∈ A, a n * phase n (t - u)‖ ^ 2) ≤
      ∑ n ∈ A, ∑ m ∈ A, ‖∑ t ∈ W, phase ((n : ℝ) / m) t‖ ^ 2 := by
  have hh := gram_energy_le A W (fun n t => phase n t) a ha
  calc
    _ ≤ ∑ n ∈ A, ∑ m ∈ A, ‖∑ t ∈ W, phase n t * star (phase m t)‖ ^ 2 := by
      simpa only [mul_assoc, phase_time_difference] using hh
    _ = _ := by
      pm_90 sum_congr n hn m hm
      congr 2
      apply sum_congr rfl
      intro t _
      exact phase_frequency_ratio (by exact_mod_cast hA n hn) (by exact_mod_cast hA m hm) t

end Montgomery.RationalMoment
