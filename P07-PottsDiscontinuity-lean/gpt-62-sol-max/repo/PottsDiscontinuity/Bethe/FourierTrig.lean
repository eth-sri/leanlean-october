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

@[expose] public section

open Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

/-- Termwise integration over `[-π, π]` of a series of continuous functions with a summable
uniform bound. -/
theorem hasSum_intervalIntegral_of_boundOn {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, Continuous (F n)) (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ n β, β ∈ uIoc (-π) π → |F n β| ≤ b n)
    (hsum : ∀ β, HasSum (fun n => F n β) (f β)) :
    HasSum (fun n => ∫ β in (-π)..π, F n β) (∫ β in (-π)..π, f β) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -π) (b := π)
    (fun n _ => b n) (fun n => (hF n).aestronglyMeasurable) ?_ ?_ ?_ ?_
  · simpa using fun n => ae_of_all volume (hbound n)
  · simp_all
  · exact intervalIntegrable_const
  simp_all

/-- The trigonometric series `a₀ + ∑_{n≥0} (a_n cos((n+1)α) + b_n sin((n+1)α))`. -/
noncomputable def trigSeries (a₀ : ℝ) (a b : ℕ → ℝ) (α : ℝ) : ℝ :=
  a₀ + ∑' n : ℕ, (a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) + b n * Real.sin (((n + 1 : ℕ) : ℝ) * α))

theorem continuous_trigSeries {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ) :
    Continuous (trigSeries a₀ a b) := by
  unfold trigSeries
  refine continuous_const.add ?_
  exact continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b)

section

variable (a b : ℕ → ℝ)


theorem integral_trigTerm (n : ℕ) :
    ∫ β in (-π)..π, trigTerm a b n β = 0 := by
  simpa only [mul_one, cosCoeff, sinCoeff, one_mul, integral_cos_nat_mul (Nat.succ_ne_zero n),
    integral_sin_nat_mul, mul_zero, add_zero] using
    integral_trigTerm_mul a b n (g := fun _ => 1) intervalIntegrable_const

theorem integral_trigTerm_mul_cos (n m : ℕ) :
    ∫ β in (-π)..π, trigTerm a b n β * Real.cos (((m + 1 : ℕ) : ℝ) * β) =
      if n = m then π * a n else 0 := by
  rw [integral_trigTerm_mul a b n (Continuous.intervalIntegrable (by fun_prop) _ _), cosCoeff, sinCoeff,
    integral_cos_mul_cos_pos (by omega) (by omega)]
  simp_rw [mul_comm (Real.cos _) (Real.sin _), integral_sin_mul_cos_nat]
  rcases eq_or_ne n m with rfl | h
  · simp [mul_comm]
  · simp [h, h.symm]

theorem integral_trigTerm_mul_sin (n m : ℕ) :
    ∫ β in (-π)..π, trigTerm a b n β * Real.sin (((m + 1 : ℕ) : ℝ) * β) =
      if n = m then π * b n else 0 := by
  rw [integral_trigTerm_mul a b n (Continuous.intervalIntegrable (by fun_prop) _ _), cosCoeff, sinCoeff,
    integral_sin_mul_cos_nat, integral_sin_mul_sin_pos (by omega) (by omega)]
  rcases eq_or_ne n m with rfl | h
  · simp [mul_comm]
  · simp [h, h.symm]

end

private theorem integral_trigSeries_mul {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (a₀ : ℝ) {g : ℝ → ℝ} (hg : Continuous g) {v : ℝ}
    (hv : HasSum (fun n => ∫ β in (-π)..π, trigTerm a b n β * g β) v) :
    ∫ β in (-π)..π, trigSeries a₀ a b β * g β =
      a₀ * (∫ β in (-π)..π, g β) + v := by
  have hc := continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b)
  have hs := hasSum_integral_trigTerm_mul ha hb (hg.intervalIntegrable _ _) (hasSum_trigTerm ha hb)
  change (∫ β in (-π)..π, (a₀ + ∑' n, trigTerm a b n β) * g β) = _
  simp only [add_mul]
  rw [intervalIntegral.integral_add (hg.const_mul a₀ |>.intervalIntegrable _ _)
    ((hc.fun_mul hg).intervalIntegrable _ _), intervalIntegral.integral_const_mul, hs.unique hv]

/-- The constant coefficient of a trigonometric series. -/
theorem cosCoeff_trigSeries_zero {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ) :
    cosCoeff (trigSeries a₀ a b) 0 = 2 * π * a₀ := by
  have h := integral_trigSeries_mul ha hb a₀ (g := fun _ => 1) continuous_const
    (v := 0) (by simp [integral_trigTerm])
  simp [cosCoeff, intervalIntegral.integral_const, smul_eq_mul] at h ⊢
  linarith

private theorem hasSum_single_mode {f : ℕ → ℝ} (m : ℕ) :
    HasSum (fun n => if n = m then f n else 0) (f m) := by
  simpa using hasSum_single (f := fun n => if n = m then f n else 0) m (by simp_all)

theorem cosCoeff_trigSeries_succ {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ)
    (m : ℕ) : cosCoeff (trigSeries a₀ a b) (m + 1) = π * a m := by
  unfold cosCoeff
  rw [integral_trigSeries_mul ha hb a₀ (by fun_prop)
    (by simpa only [integral_trigTerm_mul_cos] using hasSum_single_mode (f := (π * a ·)) m),
    integral_cos_nat_mul (Nat.succ_ne_zero m), mul_zero, zero_add]

theorem sinCoeff_trigSeries_succ {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ)
    (m : ℕ) : sinCoeff (trigSeries a₀ a b) (m + 1) = π * b m := by
  unfold sinCoeff
  rw [integral_trigSeries_mul ha hb a₀ (by fun_prop)
    (by simpa only [integral_trigTerm_mul_sin] using hasSum_single_mode (f := (π * b ·)) m),
    integral_sin_nat_mul, mul_zero, zero_add]

theorem summable_pow_succ_mul {a : ℕ → ℝ} (ha : Summable a) {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    Summable (fun n : ℕ => c ^ (n + 1) * a n) := by
  refine Summable.of_norm_bounded (g := fun n => |a n|) ha.abs ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ c ^ (n + 1))]
  calc c ^ (n + 1) * |a n| ≤ 1 * |a n| := by
        gcongr; exact pow_le_one₀ h0 h1
    _ = |a n| := one_mul _

/-- The Poisson convolution acts diagonally on trigonometric series:
`Ξ_μ * (a₀ + ∑ a_n cos((n+1)·) + b_n sin((n+1)·))/(2π) = a₀ + ∑ e^{-μ(n+1)} (a_n cos + b_n sin)`
(the coefficient statement `\widehat{Ξ_μ * g}(m) = e^{-μ|m|} ĝ(m)`). -/
theorem xiConv_trigSeries {μ : ℝ} (hμ : 0 < μ) {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (a₀ α : ℝ) :
    xiConv μ (trigSeries a₀ a b) α = trigSeries a₀ (fun n => Real.exp (-μ) ^ (n + 1) * a n)
      (fun n => Real.exp (-μ) ^ (n + 1) * b n) α := by
  have h := (hasSum_xiConv hμ ((continuous_trigSeries ha hb a₀).intervalIntegrable _ _) α).tsum_eq
  simp_rw [cosCoeff_trigSeries_succ ha hb, sinCoeff_trigSeries_succ ha hb,
    cosCoeff_trigSeries_zero ha hb, show (2 * π)⁻¹ * (2 * π * a₀) = a₀ by field_simp] at h
  rw [← (eq_sub_iff_add_eq.mp h)]
  unfold trigSeries
  rw [add_comm a₀]
  congr 1
  apply tsum_congr
  intro n
  field_simp

/-- Adding a series to its Poisson convolution scales each nonconstant
coefficient by one plus the Poisson multiplier. -/
theorem trigSeries_add_xiConv {μ : ℝ} (hμ : 0 < μ) {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (a₀ α : ℝ) :
    trigSeries a₀ a b α + xiConv μ (trigSeries a₀ a b) α =
      trigSeries (2 * a₀) (fun n => (1 + Real.exp (-μ) ^ (n + 1)) * a n)
        (fun n => (1 + Real.exp (-μ) ^ (n + 1)) * b n) α := by
  rw [xiConv_trigSeries hμ ha hb]
  have hr : Real.exp (-μ) ≤ 1 := by simp [hμ.le]
  have h := (hasSum_trigTerm ha hb α).add
    (hasSum_trigTerm (summable_pow_succ_mul ha (Real.exp_pos _).le hr)
      (summable_pow_succ_mul hb (Real.exp_pos _).le hr) α)
  have he (n : ℕ) := show trigTerm a b n α +
      trigTerm (fun j => Real.exp (-μ) ^ (j + 1) * a j) (fun j => Real.exp (-μ) ^ (j + 1) * b j) n α =
      trigTerm (fun j => (1 + Real.exp (-μ) ^ (j + 1)) * a j)
        (fun j => (1 + Real.exp (-μ) ^ (j + 1)) * b j) n α by unfold trigTerm; ring
  simp_rw [he] at h
  unfold trigSeries
  simp only [trigTerm] at h
  rw [h.tsum_eq]
  ring

end PottsDiscontinuity.Bethe
