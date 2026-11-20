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
theorem hasSum_intervalIntegral_of_bound {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, Continuous (F n)) (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ n β, |F n β| ≤ b n) (hsum : ∀ β, HasSum (fun n => F n β) (f β)) :
    HasSum (fun n => ∫ β in (-π)..π, F n β) (∫ β in (-π)..π, f β) := by
  refine intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -π) (b := π)
    (fun n _ => b n) (by fun_prop) ?_ ?_ ?_ ?_
  · simp_all
  · solve_by_elim [Filter.Eventually.of_forall]
  · exact intervalIntegrable_const
  · solve_by_elim [Filter.Eventually.of_forall]

section
variable (a₀ : ℝ) (a b : ℕ → ℝ) (n : ℕ) (α : ℝ)
include a b

include a₀ α in
/-- The trigonometric series `a₀ + ∑_{n≥0} (a_n cos((n+1)α) + b_n sin((n+1)α))`. -/
noncomputable def trigSeries : ℝ :=
  a₀ + ∑' n : ℕ, (a n * Real.cos ((n + 1 : ℕ) * α) + b n * Real.sin ((n + 1 : ℕ) * α))

include n α in
/-- The general term of a trigonometric series. -/
noncomputable def trigTerm : ℝ :=
  a n * Real.cos ((n + 1 : ℕ) * α) + b n * Real.sin ((n + 1 : ℕ) * α)

theorem abs_trigTerm_le : |trigTerm a b n α| ≤ |a n| + |b n| := by
  let product := ((n + 1 : ℕ) : ℝ) * α
  calc |a n * Real.cos (product) + b n * Real.sin (product)|
      ≤ |a n * Real.cos (product)| + |b n * Real.sin (product)| :=
        abs_add_le _ _
    _ ≤ _ := by
        rw [abs_mul, abs_mul]
        gcongr
        · calc |a n| * |Real.cos (product)| ≤ |a n| * 1 := by
                gcongr; exact Real.abs_cos_le_one _
            _ = _ := mul_one _
        · calc |b n| * |Real.sin (product)| ≤ |b n| * 1 := by
                gcongr; exact Real.abs_sin_le_one _
            _ = _ := mul_one _

theorem continuous_trigTerm : Continuous (trigTerm a b n) := by
  unfold trigTerm; fun_prop

end

variable {μ : ℝ} (hμ : 0 < μ) {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ) (m : ℕ)

include ha hb in
theorem hasSum_trigTerm (α : ℝ) :
    HasSum (fun n => trigTerm a b n α) (∑' n, trigTerm a b n α) := Summable.hasSum (Summable.of_norm_bounded (Summable.add (Summable.abs ha) (Summable.abs hb)) fun n => abs_trigTerm_le a b n α)

include ha hb in
theorem continuous_trigSeries :
    Continuous (trigSeries a₀ a b) := by
  exact continuous_const.add (continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b))


theorem integral_trigTerm (a b : ℕ → ℝ) (n : ℕ) :
    ∫ β in (-π)..π, trigTerm a b n β = 0 := by
  unfold trigTerm
  rw [intervalIntegral.integral_add ((intervalIntegrable_cos_mul _).const_mul _)
    ((intervalIntegrable_sin_mul _).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos_nat_mul (by omega), integral_sin_nat_mul]
  simp

theorem integral_trigTerm_mul_cos (a b : ℕ → ℝ) (n m : ℕ) :
    ∫ β in (-π)..π, trigTerm a b n β * Real.cos ((m + 1 : ℕ) * β) =
      if n = m then π * a n else 0 := by
  have h1 : ∀ β : ℝ, trigTerm a b n β * Real.cos ((m + 1 : ℕ) * β) =
      a n * (Real.cos ((n + 1 : ℕ) * β) * Real.cos ((m + 1 : ℕ) * β)) +
        b n * (Real.sin ((n + 1 : ℕ) * β) * Real.cos ((m + 1 : ℕ) * β)) := by
    grind [trigTerm]
  simp_rw [h1]
  have hi1 : IntervalIntegrable (fun β : ℝ => Real.cos ((n + 1 : ℕ) * β) *
      Real.cos ((m + 1 : ℕ) * β)) volume (-π) π :=
    by apply Continuous.intervalIntegrable <;> fun_prop
  have hi2 : IntervalIntegrable (fun β : ℝ => Real.sin ((n + 1 : ℕ) * β) *
      Real.cos ((m + 1 : ℕ) * β)) volume (-π) π :=
    by apply Continuous.intervalIntegrable <;> fun_prop
  rw [intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_mul_cos_pos (by omega), integral_sin_mul_cos_nat]
  grind

theorem integral_trigTerm_mul_sin (a b : ℕ → ℝ) (n m : ℕ) :
    ∫ β in (-π)..π, trigTerm a b n β * Real.sin ((m + 1 : ℕ) * β) =
      if n = m then π * b n else 0 := by
  have h1 : ∀ β : ℝ, trigTerm a b n β * Real.sin ((m + 1 : ℕ) * β) =
      a n * (Real.sin ((m + 1 : ℕ) * β) * Real.cos ((n + 1 : ℕ) * β)) +
        b n * (Real.sin ((n + 1 : ℕ) * β) * Real.sin ((m + 1 : ℕ) * β)) := by
    grind [trigTerm]
  simp_rw [h1]
  have hi1 : IntervalIntegrable (fun β : ℝ => Real.sin ((m + 1 : ℕ) * β) *
      Real.cos ((n + 1 : ℕ) * β)) volume (-π) π :=
    by apply Continuous.intervalIntegrable <;> fun_prop
  have hi2 : IntervalIntegrable (fun β : ℝ => Real.sin ((n + 1 : ℕ) * β) *
      Real.sin ((m + 1 : ℕ) * β)) volume (-π) π :=
    by apply Continuous.intervalIntegrable <;> fun_prop
  rw [intervalIntegral.integral_add (hi1.const_mul _) (hi2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sin_mul_sin_pos (by omega), integral_sin_mul_cos_nat]
  grind

include ha hb in
/-- The constant coefficient of a trigonometric series. -/
theorem cosCoeff_trigSeries_zero :
    cosCoeff (trigSeries a₀ a b) 0 = 2 * π * a₀ := by
  have hs := hasSum_intervalIntegral_of_bound (F := fun n β => trigTerm a b n β) (continuous_trigTerm a b) _ (ha.abs.add hb.abs)
    (abs_trigTerm_le a b) (hasSum_trigTerm ha hb)
  simp_rw [integral_trigTerm] at hs
  change ∫ β in (-π)..π, (a₀ + ∑' n, trigTerm a b n β) * Real.cos ((0 : ℕ) * β) = _
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
  rw [intervalIntegral.integral_add intervalIntegrable_const ((continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b)).intervalIntegrable _ _), (hs.unique hasSum_zero)]
  simp only [add_zero, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- Project a uniformly summable trigonometric series onto a bounded, mean-zero
mode. Orthogonality singles out the coefficient at `m`. -/
private theorem project_trigSeries {a b v : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (a₀ : ℝ) (m : ℕ) (f : ℝ → ℝ) (hf : Continuous f) (hbnd : ∀ x, |f x| ≤ 1)
    (hz : ∫ x in (-π)..π, f x = 0)
    (horth : ∀ n, ∫ x in (-π)..π, trigTerm a b n x * f x = if n = m then π * v n else 0) :
    ∫ x in (-π)..π, trigSeries a₀ a b x * f x = π * v m := by
  have hs := hasSum_intervalIntegral_of_bound
    (F := fun n x => trigTerm a b n x * f x)
    (fun n => (continuous_trigTerm a b n).mul hf) _ (ha.abs.add hb.abs)
    (fun n x => by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hbnd x)).trans (abs_trigTerm_le a b n x)) (fun x => (hasSum_trigTerm ha hb x).mul_right _)
  simp_rw [horth] at hs
  have hsum := hasSum_single (f := fun n => if n = m then π * v n else 0) m (by grind)
  simp at hsum
  change ∫ x in (-π)..π, (a₀ + ∑' n, trigTerm a b n x) * f x = _
  simp_rw [add_mul]
  have hi : IntervalIntegrable (fun x => (∑' n, trigTerm a b n x) * f x) volume (-π) π :=
    ((continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b)).mul hf).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((hf.intervalIntegrable _ _).const_mul _)
    hi, intervalIntegral.integral_const_mul, hz, mul_zero,
    zero_add, hs.unique hsum]

include ha hb in
theorem cosCoeff_trigSeries_succ : cosCoeff (trigSeries a₀ a b) (m + 1) = π * a m :=
  project_trigSeries ha hb a₀ m _ (by fun_prop) (fun _ => Real.abs_cos_le_one _)
    (integral_cos_nat_mul (Nat.succ_ne_zero m)) (fun n => integral_trigTerm_mul_cos a b n m)

include ha hb in
theorem sinCoeff_trigSeries_succ : sinCoeff (trigSeries a₀ a b) (m + 1) = π * b m :=
  project_trigSeries ha hb a₀ m _ (by fun_prop) (fun _ => Real.abs_sin_le_one _)
    (integral_sin_nat_mul _) (fun n => integral_trigTerm_mul_sin a b n m)

theorem summable_pow_succ_mul {a : ℕ → ℝ} (ha : Summable a) {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    Summable (fun n : ℕ => c ^ (n + 1) * a n) := by
  refine Summable.of_norm_bounded (g := fun n => |a n|) ha.abs ?_
  intro n
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  calc _ ≤ 1 * |a n| := by
        gcongr; exact pow_le_one₀ h0 h1
    _ = _ := one_mul _

include hμ ha hb in
/-- The Poisson convolution acts diagonally on trigonometric series:
`Ξ_μ * (a₀ + ∑ a_n cos((n+1)·) + b_n sin((n+1)·))/(2π) = a₀ + ∑ e^{-μ(n+1)} (a_n cos + b_n sin)`
(the coefficient statement `\widehat{Ξ_μ * g}(m) = e^{-μ|m|} ĝ(m)`). -/
theorem xiConv_trigSeries
    (a₀ α : ℝ) :
    xiConv μ (trigSeries a₀ a b) α = trigSeries a₀ (fun n => Real.exp (-μ) ^ (n + 1) * a n)
      (fun n => Real.exp (-μ) ^ (n + 1) * b n) α := by
  have h := hasSum_xiConv hμ ((continuous_trigSeries ha hb a₀).intervalIntegrable _ _) α
  simp_rw [cosCoeff_trigSeries_succ ha hb, sinCoeff_trigSeries_succ ha hb,
    cosCoeff_trigSeries_zero ha hb] at h
  have h2 := h.tsum_eq
  have e1 : (2 * π)⁻¹ * (2 * π * a₀) = a₀ := by field_simp
  have e2 : ∀ n : ℕ, π⁻¹ * Real.exp (-μ) ^ (n + 1) *
      (Real.cos ((n + 1 : ℕ) * α) * (π * a n) + Real.sin ((n + 1 : ℕ) * α) * (π * b n)) =
      Real.exp (-μ) ^ (n + 1) * a n * Real.cos ((n + 1 : ℕ) * α) +
        Real.exp (-μ) ^ (n + 1) * b n * Real.sin ((n + 1 : ℕ) * α) := by
    intro n; field_simp
  simp_rw [e2] at h2
  have e3 : trigSeries a₀ (fun n => Real.exp (-μ) ^ (n + 1) * a n)
      (fun n => Real.exp (-μ) ^ (n + 1) * b n) α =
      a₀ + ∑' n : ℕ, (Real.exp (-μ) ^ (n + 1) * a n * Real.cos ((n + 1 : ℕ) * α) +
        Real.exp (-μ) ^ (n + 1) * b n * Real.sin ((n + 1 : ℕ) * α)) := rfl
  linarith

end PottsDiscontinuity.Bethe
