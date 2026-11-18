module

public import Mathlib
public import PottsDiscontinuity.Bethe.FourierPoisson

/-!
# Absolutely convergent trigonometric series and the Poisson convolution
-/

@[expose] public section

open Real MeasureTheory Filter Topology Set intervalIntegral

namespace PottsDiscontinuity.Bethe

private theorem hasSum_intervalIntegral_of_bound {F : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hF : ∀ n, Continuous (F n)) (b : ℕ → ℝ) (hb : Summable b)
    (hbound : ∀ n β, |F n β| ≤ b n) (hsum : ∀ β, HasSum (fun n => F n β) (f β)) :
    HasSum (fun n => ∫ β in (-π)..π, F n β) (∫ β in (-π)..π, f β) :=
  intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := -π) (b := π)
    (fun n _ => b n) (fun n => (hF n).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun β _ => by rw [Real.norm_eq_abs]; exact hbound n β)
    (Filter.Eventually.of_forall fun _ _ => hb) intervalIntegrable_const
    (Filter.Eventually.of_forall fun β _ => hsum β)

noncomputable def trigSeries (a₀ : ℝ) (a b : ℕ → ℝ) (α : ℝ) : ℝ :=
  a₀ + ∑' n : ℕ, (a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) + b n * Real.sin (((n + 1 : ℕ) : ℝ) * α))

noncomputable def trigTerm (a b : ℕ → ℝ) (n : ℕ) (α : ℝ) : ℝ :=
  a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) + b n * Real.sin (((n + 1 : ℕ) : ℝ) * α)

theorem abs_trigTerm_le (a b : ℕ → ℝ) (n : ℕ) (α : ℝ) : |trigTerm a b n α| ≤ |a n| + |b n| := by
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
    (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))

private theorem continuous_trigTerm (a b : ℕ → ℝ) (n : ℕ) : Continuous (trigTerm a b n) := by
  unfold trigTerm; fun_prop

theorem hasSum_trigTerm {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (α : ℝ) :
    HasSum (fun n => trigTerm a b n α) (∑' n, trigTerm a b n α) :=
  (Summable.of_norm_bounded (ha.abs.add hb.abs) fun n => by
    rw [Real.norm_eq_abs]; exact abs_trigTerm_le a b n α).hasSum

theorem continuous_trigSeries {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ) :
    Continuous (trigSeries a₀ a b) :=
  continuous_const.add (continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b))

theorem cosCoeff_trigSeries_zero {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ) :
    cosCoeff (trigSeries a₀ a b) 0 = 2 * π * a₀ := by
  have hs := hasSum_intervalIntegral_of_bound (continuous_trigTerm a b) _ (ha.abs.add hb.abs)
    (abs_trigTerm_le a b) (hasSum_trigTerm ha hb)
  have hterm0 (n : ℕ) : ∫ β in (-π)..π, trigTerm a b n β = 0 := by
    unfold trigTerm
    rw [intervalIntegral.integral_add ((intervalIntegrable_cos_mul _).const_mul _)
      ((intervalIntegrable_sin_mul _).const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_cos_nat_mul (by omega), integral_sin_nat_mul]; simp
  simp_rw [hterm0] at hs
  have hcont := continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b)
  change ∫ β in (-π)..π, (a₀ + ∑' n, trigTerm a b n β) * Real.cos (((0 : ℕ) : ℝ) * β) = _
  simp only [Nat.cast_zero, zero_mul, Real.cos_zero, mul_one]
  rw [intervalIntegral.integral_add intervalIntegrable_const (hcont.intervalIntegrable _ _),
    hs.unique hasSum_zero, add_zero, intervalIntegral.integral_const, smul_eq_mul]; ring

private theorem coeff_trigSeries_aux {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (hφ1 : ∀ β, |φ β| ≤ 1) (hφ0 : ∫ β in (-π)..π, φ β = 0)
    (c : ℝ) (m : ℕ) (hterm : ∀ n, ∫ β in (-π)..π, trigTerm a b n β * φ β = if n = m then π * c else 0) :
    (∫ β in (-π)..π, trigSeries a₀ a b β * φ β) = π * c := by
  have hcont := continuous_tsum (continuous_trigTerm a b) (ha.abs.add hb.abs) (abs_trigTerm_le a b)
  have hs := hasSum_intervalIntegral_of_bound (F := fun n β => trigTerm a b n β * φ β)
    (f := fun β => (∑' n, trigTerm a b n β) * φ β)
    (fun n => (continuous_trigTerm a b n).mul hφ) _ (ha.abs.add hb.abs)
    (fun n β => by rw [abs_mul]; exact (mul_le_of_le_one_right (abs_nonneg _) (hφ1 β)).trans (abs_trigTerm_le a b n β))
    (fun β => (hasSum_trigTerm ha hb β).mul_right _)
  simp_rw [hterm] at hs
  have hsingle := hasSum_single m (f := fun n => if n = m then π * c else 0) fun n hn => ite_eq_right hn
  rw [ite_eq_left rfl] at hsingle
  have hsum_eq : (∫ β in (-π)..π, (∑' n, trigTerm a b n β) * φ β) = π * c := hs.unique hsingle
  change (∫ β in (-π)..π, (a₀ + ∑' n, trigTerm a b n β) * φ β) = _
  simp_rw [add_mul]
  have hI2 : IntervalIntegrable (fun β => (∑' n, trigTerm a b n β) * φ β) volume (-π) π :=
    (Continuous.mul hcont hφ).intervalIntegrable _ _
  rw [intervalIntegral.integral_add ((hφ.intervalIntegrable _ _).const_mul _) hI2,
    intervalIntegral.integral_const_mul, hφ0, mul_zero, zero_add, hsum_eq]

theorem cosCoeff_trigSeries_succ {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ) (m : ℕ) :
    cosCoeff (trigSeries a₀ a b) (m + 1) = π * a m := by
  refine coeff_trigSeries_aux ha hb a₀ (fun β => Real.cos (((m + 1 : ℕ) : ℝ) * β)) (by fun_prop)
    (fun _ => Real.abs_cos_le_one _) (integral_cos_nat_mul (by omega)) (a m) m fun n => ?_
  have h1 (β : ℝ) : trigTerm a b n β * Real.cos (((m + 1 : ℕ) : ℝ) * β) =
      a n * (Real.cos (((n + 1 : ℕ) : ℝ) * β) * Real.cos (((m + 1 : ℕ) : ℝ) * β)) +
        b n * (Real.sin (((n + 1 : ℕ) : ℝ) * β) * Real.cos (((m + 1 : ℕ) : ℝ) * β)) := by unfold trigTerm; ring
  simp_rw [h1]
  rw [intervalIntegral.integral_add (((Continuous.intervalIntegrable (by fun_prop) _ _)).const_mul _)
    (((Continuous.intervalIntegrable (by fun_prop) _ _)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_cos_mul_cos_pos (by omega) (by omega), integral_sin_mul_cos_nat]
  by_cases h : n = m <;> simp [h, mul_comm]

private theorem sinCoeff_trigSeries_succ {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b) (a₀ : ℝ) (m : ℕ) :
    sinCoeff (trigSeries a₀ a b) (m + 1) = π * b m := by
  refine coeff_trigSeries_aux ha hb a₀ (fun β => Real.sin (((m + 1 : ℕ) : ℝ) * β)) (by fun_prop)
    (fun _ => Real.abs_sin_le_one _) (integral_sin_nat_mul _) (b m) m fun n => ?_
  have h1 (β : ℝ) : trigTerm a b n β * Real.sin (((m + 1 : ℕ) : ℝ) * β) =
      a n * (Real.sin (((m + 1 : ℕ) : ℝ) * β) * Real.cos (((n + 1 : ℕ) : ℝ) * β)) +
        b n * (Real.sin (((n + 1 : ℕ) : ℝ) * β) * Real.sin (((m + 1 : ℕ) : ℝ) * β)) := by unfold trigTerm; ring
  simp_rw [h1]
  rw [intervalIntegral.integral_add (((Continuous.intervalIntegrable (by fun_prop) _ _)).const_mul _)
    (((Continuous.intervalIntegrable (by fun_prop) _ _)).const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sin_mul_cos_nat, integral_sin_mul_sin_pos (by omega) (by omega)]
  by_cases h : n = m <;> simp [h, mul_comm]

theorem summable_pow_succ_mul {a : ℕ → ℝ} (ha : Summable a) {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) :
    Summable (fun n : ℕ => c ^ (n + 1) * a n) :=
  Summable.of_norm_bounded ha.abs fun n => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ h0 h1)

theorem xiConv_trigSeries {μ : ℝ} (hμ : 0 < μ) {a b : ℕ → ℝ} (ha : Summable a) (hb : Summable b)
    (a₀ α : ℝ) :
    xiConv μ (trigSeries a₀ a b) α = trigSeries a₀ (fun n => Real.exp (-μ) ^ (n + 1) * a n)
      (fun n => Real.exp (-μ) ^ (n + 1) * b n) α := by
  have hpi : π ≠ 0 := Real.pi_pos.ne'
  have h := hasSum_xiConv hμ ((continuous_trigSeries ha hb a₀).intervalIntegrable _ _) α
  simp_rw [cosCoeff_trigSeries_succ ha hb, sinCoeff_trigSeries_succ ha hb, cosCoeff_trigSeries_zero ha hb] at h
  have h2 := h.tsum_eq
  rw [show (2 * π)⁻¹ * (2 * π * a₀) = a₀ by field_simp] at h2
  simp_rw [show ∀ n : ℕ, π⁻¹ * Real.exp (-μ) ^ (n + 1) *
      (Real.cos (((n + 1 : ℕ) : ℝ) * α) * (π * a n) + Real.sin (((n + 1 : ℕ) : ℝ) * α) * (π * b n)) =
      Real.exp (-μ) ^ (n + 1) * a n * Real.cos (((n + 1 : ℕ) : ℝ) * α) +
        Real.exp (-μ) ^ (n + 1) * b n * Real.sin (((n + 1 : ℕ) : ℝ) * α) by intro; field_simp] at h2
  conv_rhs => unfold trigSeries; dsimp only
  linarith

end PottsDiscontinuity.Bethe
