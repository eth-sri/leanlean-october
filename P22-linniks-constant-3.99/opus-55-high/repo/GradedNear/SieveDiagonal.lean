module

public import GradedNear.SieveBasic

/-!
# (B) The diagonal of the sieve part: Graham's estimate and partial summation

From `Σ_{n ≤ N} ν_V(n) = N / log V + O(N / log² V)` (`GrahamEstimate`), partial summation gives
`Σ_{A ≤ n ≤ B} (log n / n) ν_V(n) ≤ (log² B - log² A) / (2 log V) + O((log² B + 1) / log² V)`
for `V₀ ≤ V ≤ A ≤ B`.

## Proof outline

* Enlarge the range `[⌈A⌉, ⌊B⌋]` to `[⌊A⌋, ⌊B⌋] = {⌊A⌋} ∪ (⌊A⌋, ⌊B⌋]` (all terms are `≥ 0`).
* The single term `n = ⌊A⌋` is at most `(2 log A / A) · S(A) ≤ 2 log A (1/log V + C/log² V)`,
  where `S(N) = Σ_{1 ≤ n ≤ N} ν_V(n)`.
* On `(⌊A⌋, ⌊B⌋]` apply Abel summation (`sum_mul_eq_sub_sub_integral_mul`) with the weight
  `F(t) = log t / t`, whose derivative `(1 - log t)/t²` is `≤ 0` for `t ≥ e`, and bound
  `S(t)` from above and below by Graham's estimate.
* The main term is `(1 / log V) ∫_A^B log t / t dt = (log² B - log² A) / (2 log V)`; all other
  terms are `O((log² B + 1) / log² V)` because `1 ≤ log V ≤ log A ≤ log B`.
-/

@[expose] public section

namespace GradedNear

open Finset MeasureTheory

theorem sieve_diagonal (hGr : GrahamEstimate) :
    ∃ C V₀ : ℝ, 0 ≤ C ∧ ∀ V A B : ℝ, V₀ ≤ V → V ≤ A → A ≤ B →
      ∑ n ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, Real.log n / n * sieveNu V n ≤
        (Real.log B ^ 2 - Real.log A ^ 2) / (2 * Real.log V) +
          C * (Real.log B ^ 2 + 1) / Real.log V ^ 2 := by
  obtain ⟨C₀, V₁, hC₀⟩ := hGr
  refine ⟨3 + 3 * max C₀ 0, max V₁ (Real.exp 1), by positivity, fun V A B hV hVA hAB => ?_⟩
  set C := max C₀ 0
  set L := Real.log V
  have hC₁ : 0 ≤ C := le_max_right ..
  have hVe : Real.exp 1 ≤ V := (le_max_right ..).trans hV
  have hV0 := (Real.exp_pos 1).trans_le hVe
  have hA0 := hV0.trans_le hVA
  have hA1 : 1 ≤ A := by linarith [Real.add_one_le_exp 1]
  have hL1 : 1 ≤ L := (Real.le_log_iff_exp_le hV0).2 hVe
  have hLa : L ≤ Real.log A := Real.log_le_log hV0 hVA
  have hab : Real.log A ≤ Real.log B := Real.log_le_log hA0 hAB
  set a := Real.log A
  set b := Real.log B
  have hK : 0 ≤ 1 / L + C / L ^ 2 := by positivity
  set K := 1 / L + C / L ^ 2 with hKd
  have hS : ∀ N, V ≤ N → ∑ k ∈ Icc 0 ⌊N⌋₊, sieveNu V k ≤
      N * K := fun N hN => by
    have h1 := (abs_le.1 (hC₀ V N (le_trans (le_max_left ..) hV) hN)).2
    have h2 : C₀ * N / L ^ 2 ≤ C * N / L ^ 2 := by
      gcongr <;> grind
    rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, ← Finset.Icc_add_one_left_eq_Ioc]
    simp [sieveNu] at h1 ⊢
    grind
  have hd : ∀ t ∈ Set.Icc A B, HasDerivAt (fun t : ℝ => Real.log t / t)
      ((1 - Real.log t) / t ^ 2) t := fun t ht => by
    have := hA0.trans_le ht.1
    convert (Real.hasDerivAt_log this.ne').div (hasDerivAt_id' t) this.ne' using 1
    field_simp
  have hcf : ContinuousOn (fun t : ℝ => Real.log t / t) (Set.Icc A B) := fun t ht =>
    (hd t ht).continuousAt.continuousWithinAt
  have hint : IntegrableOn (deriv fun t : ℝ => Real.log t / t) (Set.Icc A B) :=
    (ContinuousOn.integrableOn_Icc fun t ht => by
      have := hA0.trans_le ht.1
      exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))).congr_fun
      (fun t ht => (hd t ht).deriv.symm) measurableSet_Icc
  have hFTC : ∫ t in Set.Ioc A B, Real.log t / t = (b ^ 2 - a ^ 2) / 2 := by
    rw [← intervalIntegral.integral_of_le hAB, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => Real.log t ^ 2 / 2) (fun t ht => ?_) (hcf.intervalIntegrable_of_Icc hAB)]
    · ring
    have := hA0.trans_le (Set.uIcc_of_le hAB ▸ ht).1
    convert ((Real.hasDerivAt_log this.ne').pow 2).div_const 2 using 1
    ring
  have hI : -(∫ t in Set.Ioc A B, deriv (fun t : ℝ => Real.log t / t) t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, sieveNu V k) ≤ K *
      ((b ^ 2 - a ^ 2) / 2) := by
    rw [← integral_neg, ← hFTC, ← integral_const_mul]
    refine setIntegral_mono_on ((integrableOn_mul_sum_Icc _ hA0.le hint).mono_set
      Set.Ioc_subset_Icc_self).neg ((hcf.integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self).const_mul _) measurableSet_Ioc fun t ht => ?_
    have ht0 := hA0.trans ht.1
    have hlt : 1 ≤ Real.log t := hL1.trans (Real.log_le_log (by linarith) (hVA.trans ht.1.le))
    have := mul_le_mul (by linarith : Real.log t - 1 ≤ Real.log t) (hS t (hVA.trans ht.1.le))
      (Finset.sum_nonneg fun i _ => sieveNu_nonneg V i) (by linarith)
    rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]
    field_simp
    nlinarith
  have hm : (1 : ℝ) ≤ ⌊A⌋₊ := mod_cast (Nat.one_le_floor_iff A).2 hA1
  have hE : Real.log ⌊A⌋₊ / ⌊A⌋₊ * sieveNu V ⌊A⌋₊ ≤
      2 * a * K := by
    have h1 := (Finset.single_le_sum (fun i _ => sieveNu_nonneg V i)
      (Finset.mem_Icc.2 ⟨Nat.zero_le _, le_rfl⟩)).trans (hS A hVA)
    have h2 : A ≤ 2 * ⌊A⌋₊ := by linarith [Nat.lt_floor_add_one A]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith [mul_le_mul (Real.log_le_log (by linarith) (Nat.floor_le hA0.le)) h1
      (sieveNu_nonneg ..) (Real.log_nonneg hA1),
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hK) (Real.log_nonneg hA1)]
  have hB := mul_le_mul_of_nonneg_left (hS B (hVA.trans hAB))
    (div_nonneg (Real.log_nonneg (hA1.trans hAB)) (by linarith : 0 ≤ B))
  have hAt := mul_nonneg (div_nonneg (Real.log_nonneg hA1) hA0.le)
    (Finset.sum_nonneg fun i (_ : i ∈ Icc 0 ⌊A⌋₊) => sieveNu_nonneg V i)
  have hAbel := sum_mul_eq_sub_sub_integral_mul (sieveNu V) hA0.le hAB
    (fun t ht => (hd t ht).differentiableAt) hint
  have step1 := (Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => Real.log n / n * sieveNu V n) (Finset.Icc_subset_Icc
    (Nat.floor_le_ceil A) le_rfl) fun n (_ : n ∈ Icc ⌊A⌋₊ ⌊B⌋₊) _ =>
      mul_nonneg (by positivity) (sieveNu_nonneg V n)).trans_eq
    (by rw [Finset.Icc_eq_cons_Ioc (Nat.floor_le_floor hAB), Finset.sum_cons])
  have e : b / B * (B * K) = b * K := by field_simp [(hA0.trans_le hAB).ne']
  have key : (2 * a + b + (b ^ 2 - a ^ 2) / 2) * K ≤
      (b ^ 2 - a ^ 2) / (2 * L) + (3 + 3 * C) * (b ^ 2 + 1) / L ^ 2 := by
    rw [hKd, ← sub_nonneg]
    field_simp
    nlinarith [mul_nonneg hC₁ (sq_nonneg (b - 1))]
  linarith

end GradedNear
