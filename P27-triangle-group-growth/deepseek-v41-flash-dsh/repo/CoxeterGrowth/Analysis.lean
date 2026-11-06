module
public import Mathlib

@[expose] public section
/-!
# The plastic number and asymptotic growth rates

Existence and uniqueness of the plastic number `ρ` (the real root `> 1` of `x³ = x + 1`), and the
standard lemma that a sequence sandwiched between `c τⁿ` and `C τⁿ` has `n`-th roots tending to `τ`.
-/

namespace CoxeterGrowth

open Filter Topology

theorem exists_plastic_root : ∃ x ∈ Set.Icc (1 : ℝ) 2, x ^ 3 - x - 1 = 0 := by
  have hc : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc 1 2) := by fun_prop
  exact intermediate_value_Icc (by norm_num) hc (by constructor <;> norm_num)

/-- The plastic number: the real root `> 1` of `x³ − x − 1`. -/
noncomputable def plasticNumber : ℝ := Classical.choose exists_plastic_root

theorem plasticNumber_cubic : plasticNumber ^ 3 = plasticNumber + 1 := by
  have h := (Classical.choose_spec exists_plastic_root).2
  simp only [plasticNumber]
  linarith

theorem one_lt_plasticNumber : 1 < plasticNumber := by
  have h1 := (Classical.choose_spec exists_plastic_root).1
  have h3 := plasticNumber_cubic
  rcases h1.1.lt_or_eq with h | h
  · exact h
  · rw [show plasticNumber = 1 by simp only [plasticNumber, ← h]] at h3
    norm_num at h3

/-- Uniqueness among roots `> 1`. -/
theorem plasticNumber_unique {x : ℝ} (hx : 1 < x) (h : x ^ 3 = x + 1) : x = plasticNumber := by
  have h3 := plasticNumber_cubic
  have key : (x - plasticNumber) * (x ^ 2 + x * plasticNumber + plasticNumber ^ 2 - 1)
      = (x ^ 3 - x) - (plasticNumber ^ 3 - plasticNumber) := by ring
  rw [h, h3] at key
  have key0 : (x - plasticNumber) * (x ^ 2 + x * plasticNumber + plasticNumber ^ 2 - 1) = 0 := by
    linarith
  rcases mul_eq_zero.1 key0 with h' | h'
  · linarith
  · have hx0 : (0 : ℝ) < x := by linarith
    have hp0 : (0 : ℝ) < plasticNumber := by linarith [one_lt_plasticNumber]
    have hx2 : (1 : ℝ) < x * x := by nlinarith
    nlinarith [mul_pos hx0 hp0, mul_pos hp0 hp0]

theorem plastic_exists_unique : ∃! x : ℝ, 1 < x ∧ x ^ 3 = x + 1 :=
  ⟨plasticNumber, ⟨one_lt_plasticNumber, plasticNumber_cubic⟩, fun x hx =>
    plasticNumber_unique hx.1 hx.2⟩

/-- `c^{1/n} · ρ → ρ`. -/
theorem const_rpow_inv_mul_tendsto {ρ c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => c ^ ((n : ℝ)⁻¹) * ρ) atTop (𝓝 ρ) := by
  have h : Tendsto (fun n : ℕ => c ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    simpa [Function.comp_def, Real.rpow_zero] using
      (Real.continuousAt_const_rpow (b := 0) hc.ne').tendsto.comp tendsto_inv_atTop_nhds_zero_nat
  simpa using h.mul_const ρ

/-- `f(n)^{1/n} → τ` for any sequence eventually between `c τⁿ` and `C τⁿ`. -/
theorem root_tendsto_of_bounds (f : ℕ → ℕ) {τ c C : ℝ} (hτ : 0 ≤ τ) (hc : 0 < c) (hC : 0 < C)
    (hlo : ∀ᶠ n in atTop, c * τ ^ n ≤ (f n : ℝ))
    (hhi : ∀ᶠ n in atTop, (f n : ℝ) ≤ C * τ ^ n) :
    Tendsto (fun n : ℕ => (f n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 τ) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (const_rpow_inv_mul_tendsto (ρ := τ) hc) (const_rpow_inv_mul_tendsto (ρ := τ) hC)
    ?_ ?_
  · filter_upwards [hlo, eventually_ge_atTop 1] with n hn hn1
    have hn0 : n ≠ 0 := by omega
    calc c ^ ((n : ℝ)⁻¹) * τ = (c * τ ^ n) ^ ((n : ℝ)⁻¹) := by
          rw [Real.mul_rpow hc.le (pow_nonneg hτ _), Real.pow_rpow_inv_natCast hτ hn0]
      _ ≤ (f n : ℝ) ^ ((n : ℝ)⁻¹) :=
          Real.rpow_le_rpow (mul_nonneg hc.le (pow_nonneg hτ _)) hn (by positivity)
  · filter_upwards [hhi, eventually_ge_atTop 1] with n hn hn1
    have hn0 : n ≠ 0 := by omega
    calc (f n : ℝ) ^ ((n : ℝ)⁻¹) ≤ (C * τ ^ n) ^ ((n : ℝ)⁻¹) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hn (by positivity)
      _ = C ^ ((n : ℝ)⁻¹) * τ := by
          rw [Real.mul_rpow hC.le (pow_nonneg hτ _), Real.pow_rpow_inv_natCast hτ hn0]

end CoxeterGrowth
