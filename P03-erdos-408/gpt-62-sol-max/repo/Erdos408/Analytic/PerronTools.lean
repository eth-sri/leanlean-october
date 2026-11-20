module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import PrimeNumberTheoremAnd.PerronFormula

/-! The smoothed Perron formula and its tail bound, shared by the prime and integer sums. -/

@[expose] public section

namespace Erdos408.PerronTools

open Complex ArithmeticFunction DirichletCharacter MeasureTheory Set LSeries
open scoped LSeries.notation

/-- On `re s > 1`, `-(L'/L)(s, χ)` is the L-series of `χ Λ`. -/
theorem neg_logDeriv_LFunction_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    -(deriv (LFunction χ) s / LFunction χ s) = LSeries (↗χ * ↗Λ) s := by
  rw [deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs,
    LSeries_twist_vonMangoldt_eq χ hs, neg_div]

/-- On `re s = 2`, `‖x^s / (s (s + 1))‖ ≤ x² / t²` with `t = im s`. -/
private theorem norm_perron_f_le {x : ℝ} (hx : 0 < x) {t : ℝ} (ht : t ≠ 0) :
    ‖Perron.f x ((2 : ℝ) + t * I)‖ ≤ x ^ 2 / t ^ 2 := by
  set s : ℂ := (2 : ℝ) + t * I
  have hs : ‖s‖ * ‖s + 1‖ = ‖s * (s + 1)‖ := (norm_mul _ _).symm
  have h1 : |t| ≤ ‖s‖ := by simpa [s] using abs_im_le_norm s
  have h2 : |t| ≤ ‖s + 1‖ := by simpa [s] using abs_im_le_norm (s + 1)
  have h3 : t ^ 2 ≤ ‖s * (s + 1)‖ := by
    rw [← hs, ← sq_abs]
    nlinarith [abs_nonneg t]
  rw [Perron.f, norm_div, norm_cpow_eq_rpow_re_of_pos hx]
  simp only [s, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero,
    add_zero, Real.rpow_two]
  gcongr

/-- The line integral of the Perron kernel at `y > 1` is `2π (1 - 1/y)`. -/
private theorem integral_perron_f_of_one_lt {y : ℝ} (hy : 1 < y) :
    ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = 2 * Real.pi * (1 - 1 / y) := by
  have h := Perron.formulaGtOne (σ := 2) hy (by norm_num)
  rw [VerticalIntegral', VerticalIntegral, smul_eq_mul, smul_eq_mul] at h
  have hπ : (2 * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  change 1 / (2 * Real.pi * I) * (I * ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I)) = _ at h
  generalize ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = J at h ⊢
  rw [← h]
  field_simp

/-- The line integral of the Perron kernel at `0 < y < 1` vanishes. -/
private theorem integral_perron_f_of_lt_one {y : ℝ} (hy0 : 0 < y) (hy : y < 1) :
    ∫ t : ℝ, Perron.f y ((2 : ℝ) + t * I) = 0 := by
  have h := Perron.formulaLtOne (σ := 2) hy0 hy (by norm_num)
  rw [VerticalIntegral, smul_eq_mul] at h
  simpa using h

/-- A function bounded by `B / t²` on `(T, ∞)` has integral there of norm at most `B / T`. -/
private theorem norm_setIntegral_Ioi_le {g : ℝ → ℂ} {B T : ℝ} (hT : 0 < T)
    (hg : IntegrableOn g (Ioi T)) (hgB : ∀ t, T < t → ‖g t‖ ≤ B / t ^ 2) :
    ‖∫ t in Ioi T, g t‖ ≤ B / T := by
  have hrpow : IntegrableOn (fun t : ℝ ↦ t ^ (-2 : ℝ)) (Ioi T) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hT
  have hle : ∀ t ∈ Ioi T, ‖g t‖ ≤ B * t ^ (-2 : ℝ) := by
    intro t ht
    have ht0 : 0 < t := hT.trans ht
    rw [Real.rpow_neg ht0.le, Real.rpow_two, ← div_eq_mul_inv]
    exact hgB t ht
  calc ‖∫ t in Ioi T, g t‖
      ≤ ∫ t in Ioi T, ‖g t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi T, B * t ^ (-2 : ℝ) :=
        setIntegral_mono_on hg.norm (hrpow.const_mul B) measurableSet_Ioi hle
    _ = B / T := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
        norm_num [Real.rpow_neg_one, div_eq_mul_inv]

/-- To the right of `1`, the terms of the L-series of `χ Λ` are dominated by those of `Λ`. -/
theorem norm_term_twist_vonMangoldt_le {k : ℕ} (χ : DirichletCharacter ℂ k) (s : ℂ)
    (n : ℕ) : ‖term (↗χ * ↗Λ) s n‖ ≤ ‖term ↗Λ (s.re : ℂ) n‖ := by
  rw [norm_term_eq, norm_term_eq, ofReal_re]
  split_ifs
  · rfl
  have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
  gcongr
  simpa [norm_mul] using mul_le_of_le_one_left (abs_nonneg (Λ n)) hχ

/-- To the right of `1`, `‖(L'/L)(s, χ)‖ ≤ ∑ Λ(n) / n^{re s}`. -/
theorem norm_logDeriv_LFunction_le_tsum {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k)
    {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction χ) s / LFunction χ s‖ ≤ ∑' n, ‖term ↗Λ (s.re : ℂ) n‖ := by
  have hle := norm_term_twist_vonMangoldt_le χ s
  have hΛ : Summable fun n ↦ ‖term ↗Λ (s.re : ℂ) n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_vonMangoldt (by simpa using hs))
  have hsum : Summable fun n ↦ ‖term (↗χ * ↗Λ) s n‖ :=
    hΛ.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hle
  rw [← norm_neg, ← neg_div, deriv_LFunction_eq_deriv_LSeries χ hs, LFunction_eq_LSeries χ hs,
    ← LSeries_twist_vonMangoldt_eq χ hs, LSeries]
  exact (norm_tsum_le_tsum_norm hsum).trans (Summable.tsum_le_tsum hle hsum hΛ)

/-- Each term of the L-series at `s - iu` times `Y^s / (s (s + 1))` is a Perron kernel at
`Y / n`. -/
private theorem term_mul_perron_f_eq (a : ℕ → ℂ) (u : ℝ) {Y : ℝ}
    (hY : 0 < Y) {n : ℕ} (hn : n ≠ 0) (s : ℂ) :
    term a (s - u * I) n * Perron.f Y s =
      a n * (n : ℂ) ^ ((u : ℂ) * I) * Perron.f (Y / n) s := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h := Perron.f_mul_eq_f hY (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)) s
  rw [ofReal_natCast, cpow_neg] at h
  rw [term_of_ne_zero hn, ← h, cpow_sub _ _ hn0]
  field_simp

/-- Evaluate the vertical integral from the coefficients of a shifted Dirichlet series. -/
theorem verticalIntegral_perronLSeries {a : ℕ → ℂ} {F : ℂ → ℂ} {u Y : ℝ}
    (hY0 : 0 < Y) (hYN : ∀ n : ℕ, (n : ℝ) ≠ Y) (hsum₂ : LSeriesSummable a 2)
    (hF : ∀ t : ℝ, F ((2 : ℝ) + t * I) =
      LSeries a ((2 : ℝ) + t * I - u * I) * Perron.f Y ((2 : ℝ) + t * I)) :
    VerticalIntegral F 2 = 2 * Real.pi * I *
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, a n * (n : ℂ) ^ ((u : ℂ) * I) * (1 - n / Y) := by
  -- Expand the integrand as a Dirichlet series of Perron kernels.
  set g : ℕ → ℝ → ℂ := fun n t ↦
    term a ((2 : ℝ) + t * I - u * I) n * Perron.f Y ((2 : ℝ) + t * I) with hg
  have hsum : ∀ t : ℝ, F ((2 : ℝ) + t * I) = ∑' n, g n t := by
    intro t
    rw [hF t, LSeries, ← tsum_mul_right]
  have hg_eq : ∀ n, n ≠ 0 → ∀ t,
      g n t = a n * (n : ℂ) ^ ((u : ℂ) * I) * Perron.f (Y / n) ((2 : ℝ) + t * I) :=
    fun n hn t ↦ term_mul_perron_f_eq a u hY0 hn _
  -- Each term is integrable, and the integrals of the norms are summable.
  have hg_int : ∀ n, Integrable (g n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    · rw [funext (hg_eq n hn)]
      have hYn : 0 < Y / n := div_pos hY0 (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      exact (Perron.isIntegrable hYn (by norm_num) (by norm_num)).const_mul _
  have hg_norm : ∀ n, ∫ t, ‖g n t‖ =
      ‖term a 2 n‖ * ∫ t : ℝ, ‖Perron.f Y ((2 : ℝ) + t * I)‖ := by
    intro n
    rw [← integral_const_mul]
    congr 1 with t
    rw [hg, norm_mul, norm_term_eq, norm_term_eq]
    simp
  have hg_sum : Summable fun n ↦ ∫ t, ‖g n t‖ := by
    simp_rw [hg_norm]
    exact (summable_norm_iff.mpr hsum₂).mul_right _
  -- Evaluate each term with the Perron formula.
  have hg_val : ∀ n, ∫ t, g n t = if n ∈ Finset.Icc 1 ⌊Y⌋₊ then
      2 * Real.pi * (a n * (n : ℂ) ^ ((u : ℂ) * I) * (1 - n / Y)) else 0 := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hg]
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [funext (hg_eq n hn), integral_const_mul]
    split_ifs with hmem
    · have hnY : (n : ℝ) < Y :=
        lt_of_le_of_ne ((Nat.le_floor_iff hY0.le).mp (Finset.mem_Icc.mp hmem).2) (hYN n)
      rw [integral_perron_f_of_one_lt ((one_lt_div hn0).mpr hnY)]
      push_cast
      rw [one_div_div]
      ring
    · have hYn : Y < n := (Nat.floor_lt hY0.le).mp (by
        simp only [Finset.mem_Icc, not_and_or, not_le] at hmem
        omega)
      rw [integral_perron_f_of_lt_one (div_pos hY0 hn0) ((div_lt_one hn0).mpr hYn), mul_zero]
  -- Interchange the sum and the integral.
  rw [VerticalIntegral, smul_eq_mul, funext hsum,
    ← integral_tsum_of_summable_integral_norm hg_int hg_sum, tsum_congr hg_val,
    tsum_eq_sum (s := Finset.Icc 1 ⌊Y⌋₊) (fun n hn ↦ ite_eq_right hn),
    Finset.sum_congr rfl (fun n hn ↦ ite_eq_left hn), ← Finset.mul_sum]
  ring

/-- Truncate the Perron integral when its integrand is bounded by a multiple of the kernel. -/
theorem norm_perron_tail_le {F₀ : ℂ → ℂ} {A x T : ℝ} (hx0 : 0 < x) (hT0 : 0 < T)
    (hA : 0 ≤ A) (hF_int : Integrable fun t : ℝ ↦ F₀ ((2 : ℝ) + t * I))
    (hF : ∀ t : ℝ, ‖F₀ ((2 : ℝ) + t * I)‖ ≤ A * ‖Perron.f x ((2 : ℝ) + t * I)‖) :
    ‖VerticalIntegral F₀ 2 - VIntegral F₀ 2 (-T) T‖ ≤ 2 * A * x ^ 2 / T := by
  let F : ℝ → ℂ := fun t ↦ F₀ ((2 : ℝ) + t * I)
  -- Pointwise, `‖F t‖ ≤ A x² / t²`.
  have hF_le : ∀ t : ℝ, t ≠ 0 → ‖F t‖ ≤ A * x ^ 2 / t ^ 2 := by
    intro t ht
    rw [mul_div_assoc]
    exact (hF t).trans
      (mul_le_mul_of_nonneg_left (norm_perron_f_le hx0 ht) hA)
  -- Bound the two tails.
  have hupper : ‖∫ t in Ici T, F t‖ ≤ A * x ^ 2 / T := by
    rw [integral_Ici_eq_integral_Ioi]
    exact norm_setIntegral_Ioi_le hT0 hF_int.integrableOn
      fun t ht ↦ hF_le t (hT0.trans ht).ne'
  have hlower : ‖∫ t in Iic (-T), F t‖ ≤ A * x ^ 2 / T := by
    rw [← integral_comp_neg_Ioi]
    refine norm_setIntegral_Ioi_le hT0 hF_int.comp_neg.integrableOn fun t ht ↦ ?_
    rw [← neg_sq t]
    exact hF_le (-t) (neg_ne_zero.mpr (hT0.trans ht).ne')
  rw [verticalIntegral_split_three (-T) T hF_int, add_right_comm, add_sub_cancel_right]
  calc ‖I • (∫ t in Iic (-T), F t) + I • ∫ t in Ici T, F t‖
      ≤ ‖∫ t in Iic (-T), F t‖ + ‖∫ t in Ici T, F t‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        simp
    _ ≤ A * x ^ 2 / T + A * x ^ 2 / T := add_le_add hlower hupper
    _ = 2 * A * x ^ 2 / T := by ring

end Erdos408.PerronTools
