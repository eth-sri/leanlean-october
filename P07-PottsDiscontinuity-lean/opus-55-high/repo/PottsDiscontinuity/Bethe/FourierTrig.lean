module

public import Mathlib
public import PottsDiscontinuity.Bethe.FourierPoisson

/-!
# Absolutely convergent trigonometric series and the Poisson convolution

For absolutely summable coefficient sequences `a, b`, the series
`trigSeries a₀ a b α = a₀ + ∑_{n ≥ 0} (a n cos((n+1)α) + b n sin((n+1)α))` is continuous, has
Fourier coefficients `∫ g cos(m ·) = π a_{m-1}`, `∫ g sin(m ·) = π b_{m-1}`, `∫ g = 2π a₀`
(termwise integration over `[-π, π]`), and the Poisson convolution `xiConv μ` multiplies the
`m`-th coefficient by `e^{-μ m}` (`xiConv_trigSeries`).  This is the form in which the
Fourier-coefficient identities of §4 (`Ξ̂_μ(m) = e^{-μ|m|}`) are used.
-/

@[expose] public noncomputable section

open Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- The trigonometric series `a₀ + ∑_{n≥0} (a_n cos((n+1)α) + b_n sin((n+1)α))`. -/
def trigSeries (a₀ : ℝ) (a b : ℕ → ℝ) (α : ℝ) : ℝ :=
  a₀ + ∑' n : ℕ, (a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) + b n * Real.sin (((n + 1 : ℕ) : ℝ) * α))

section
variable (a b : ℕ → ℝ) (n : ℕ)
/-- The general term of a trigonometric series. -/
def trigTerm (α : ℝ) : ℝ :=
  a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) + b n * Real.sin (((n + 1 : ℕ) : ℝ) * α)

theorem abs_trigTerm_le (α : ℝ) : |trigTerm a b n α| ≤ |a n| + |b n| :=
  (abs_add_le _ _).trans (by
    rw [abs_mul, abs_mul]
    exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (abs_cos_le_one _))
      (mul_le_of_le_one_right (abs_nonneg _) (abs_sin_le_one _)))
end

section
variable {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
include ha hb
theorem hasSum_trigTerm (α : ℝ) :
    HasSum (fun n => trigTerm a b n α) (∑' n, trigTerm a b n α) :=
  (Summable.of_norm_bounded (ha.abs.add hb.abs) (abs_trigTerm_le a b · α)).hasSum

theorem continuous_trigSeries (a₀ : ℝ) :
    Continuous (trigSeries a₀ a b) :=
  continuous_const.add (continuous_tsum (fun n => by fun_prop) (ha.abs.add hb.abs)
    (abs_trigTerm_le a b))

theorem hasSum_coeff (a₀ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    HasSum (fun n => a n * cosCoeff g (n + 1) + b n * sinCoeff g (n + 1))
      ((∫ β in (-π)..π, trigSeries a₀ a b β * g β) - a₀ * ∫ β in (-π)..π, g β) := by
  convert hasSum_integral_mul (hg.intervalIntegrable _ _) (ha.abs.add hb.abs)
    (fun n => by unfold trigTerm; fun_prop) (abs_trigTerm_le a b)
    (fun β => (hasSum_trigTerm ha hb β).mul_right (g β)) using 1
  · funext n
    rw [← one_mul (a n * _ + _), ← integral_trig_mul (hg.intervalIntegrable _ _)]
    congr 1
    funext β
    simp only [trigTerm]
    ring
  · have := continuous_trigSeries ha hb a₀
    rw [← intervalIntegral.integral_const_mul, ← integral_sub
      ((by fun_prop : Continuous fun β => trigSeries a₀ a b β * g β).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun β => a₀ * g β).intervalIntegrable _ _)]
    simp only [trigSeries, trigTerm]
    ring_nf
end

section
variable {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ)
include ha hb
theorem cosCoeff_trigSeries_zero  :
    cosCoeff (trigSeries a₀ a b) 0 = 2 * π * a₀ := by
  have h := (hasSum_coeff ha hb a₀ (g := fun _ => 1) continuous_const).unique (by
    convert hasSum_zero with n
    simp only [cosCoeff, sinCoeff, one_mul]
    rw [integral_cos_nat_mul n.succ_ne_zero, integral_sin_nat_mul]
    ring)
  rw [cosCoeff_zero]
  simp at h
  linarith

theorem cosCoeff_trigSeries_succ (m : ℕ) : cosCoeff (trigSeries a₀ a b) (m + 1) = π * a m := by
  have h := (hasSum_coeff ha hb a₀ (by fun_prop : Continuous fun β => cos (((m + 1 : ℕ) : ℝ) * β))).unique (by
    convert hasSum_ite_eq m (π * a m) with n
    rw [cosCoeff, sinCoeff]
    simp_rw [mul_comm (cos _) (sin _), integral_sin_mul_cos_nat, integral_cos_mul_cos_pos n.succ_ne_zero]
    split_ifs <;> simp_all [mul_comm])
  rw [integral_cos_nat_mul m.succ_ne_zero] at h
  rw [cosCoeff]
  linarith

theorem sinCoeff_trigSeries_succ (m : ℕ) : sinCoeff (trigSeries a₀ a b) (m + 1) = π * b m := by
  have h := (hasSum_coeff ha hb a₀ (by fun_prop : Continuous fun β => sin (((m + 1 : ℕ) : ℝ) * β))).unique (by
    convert hasSum_ite_eq m (π * b m) with n
    rw [cosCoeff, sinCoeff]
    simp_rw [integral_sin_mul_cos_nat, integral_sin_mul_sin_pos n.succ_ne_zero]
    split_ifs <;> simp_all [mul_comm])
  rw [integral_sin_nat_mul] at h
  rw [sinCoeff]
  linarith
end

theorem summable_pow_succ_mul {a : ℕ → ℝ} (ha : Summable a) {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    Summable (fun n : ℕ => c ^ (n + 1) * a n) :=
  Summable.of_norm_bounded ha.abs fun n => by
    rw [norm_mul, norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ h0 h1)

/-- The Poisson convolution acts diagonally on trigonometric series:
`Ξ_μ * (a₀ + ∑ a_n cos((n+1)·) + b_n sin((n+1)·))/(2π) = a₀ + ∑ e^{-μ(n+1)} (a_n cos + b_n sin)`
(the coefficient statement `\widehat{Ξ_μ * g}(m) = e^{-μ|m|} ĝ(m)`). -/
theorem xiConv_trigSeries {μ : ℝ} (hμ : 0 < μ) {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (a₀ α : ℝ) :
    xiConv μ (trigSeries a₀ a b) α = trigSeries a₀ (fun n => Real.exp (-μ) ^ (n + 1) * a n)
      (fun n => Real.exp (-μ) ^ (n + 1) * b n) α := by
  have h := hasSum_xiConv hμ ((continuous_trigSeries ha hb a₀).intervalIntegrable _ _) α
  simp_rw [cosCoeff_trigSeries_succ ha hb, sinCoeff_trigSeries_succ ha hb,
    cosCoeff_trigSeries_zero ha hb, show (2 * π)⁻¹ * (2 * π * a₀) = a₀ by field_simp] at h
  rw [trigSeries, ← sub_eq_iff_eq_add', ← h.tsum_eq]
  congr 1
  funext n
  field_simp
end PottsDiscontinuity.Bethe
