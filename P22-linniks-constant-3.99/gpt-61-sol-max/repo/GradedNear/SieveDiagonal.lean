import GradedNear.Tactics

import GradedNear.SieveBasic

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

namespace GradedNear

open Finset MeasureTheory

/-! ## Calculus of `log t / t` -/

/-! ## The core estimate for a fixed level `V` -/

theorem sieve_diagonal (hGr : GrahamEstimate) :
    ∃ C V₀ : ℝ, 1 < V₀ ∧ ∀ V A B : ℝ, V₀ ≤ V → V ≤ A → A ≤ B →
      ∑ n ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, Real.log n / n * sieveNu V n ≤
        (Real.log B ^ 2 - Real.log A ^ 2) / (2 * Real.log V) +
          C * (Real.log B ^ 2 + 1) / Real.log V ^ 2 := by
  obtain ⟨C₀, V₁, hC₀⟩ := hGr
  let C₁ := max C₀ 0
  refine ⟨3 + 3 * C₁, max V₁ (Real.exp 1), ?_, ?_⟩
  · simp_all
  · intro V A B hV hVA hAB
    let ℓ := Real.log V
    let F (t : ℝ) := Real.log t / t

    have hVe := le_of_max_le_right hV
    have hV0 := le_trans (Real.exp_pos 1).le hVe
    have hC₁ := le_max_right C₀ 0
    let S (N : ℝ) := ∑ n ∈ Finset.Icc 0 ⌊N⌋₊, sieveNu V n
    have hS (N : ℝ) (hN : V ≤ N) :
        N / ℓ - C₁ * N / ℓ ^ 2 ≤ S N ∧
        S N ≤ N / ℓ + C₁ * N / ℓ ^ 2 := by


      have h' : C₀ * N / ℓ ^ 2 ≤ C₁ * N / ℓ ^ 2 := by bound
      have h2 := abs_le.mp ((hC₀ V N (le_of_max_le_left hV) hN).trans h')
      simp only [S, Finset.Icc_eq_cons_Ioc (Nat.zero_le ⌊N⌋₊), Finset.sum_cons,
        sieveNu, Nat.divisors_zero, Finset.sum_empty, zero_pow two_ne_zero, zero_add,
        ← Finset.Icc_add_one_left_eq_Ioc]
      bound
    -- basic facts
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by
      grind [Real.add_one_le_exp]

    have hA2 := (h2e.trans hVe).trans hVA
    have hA0 : 0 < A := by linarith
    have hB0 : 0 < B := by linarith
    have hL1 := by
      have := Real.log_le_log (Real.exp_pos 1) hVe
      simpa [ℓ] using this

    have hLA := Real.log_le_log (by linarith) hVA
    have hlogAB := Real.log_le_log hA0 hAB
    set K := 1 / ℓ + C₁ / ℓ ^ 2
    have hK0 : 0 ≤ K := by positivity
    -- the upper bound in product form
    have hSup : ∀ N : ℝ, V ≤ N →
        S N ≤ N * K := by grind
    -- Step 1: enlarge the range of summation
    have step1 : ∑ n ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, F n * sieveNu V n ≤
        F ⌊A⌋₊ * sieveNu V ⌊A⌋₊ +
          ∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, F n * sieveNu V n := by
      have hsub : Finset.Icc ⌈A⌉₊ ⌊B⌋₊ ⊆ Finset.Icc ⌊A⌋₊ ⌊B⌋₊ :=
        Finset.Icc_subset_Icc (Nat.floor_le_ceil A) le_rfl
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_).trans_eq ?_
      · dsimp only [F]; positivity
      · rw [Finset.Icc_eq_cons_Ioc (Nat.floor_le_floor hAB), Finset.sum_cons]
    -- Step 2: Abel summation on `(A, B]`
    have hdiff : ∀ t ∈ Set.Icc A B, DifferentiableAt ℝ F t :=
      by fun_prop (disch := grind)
    have hcont : ContinuousOn (fun t : ℝ => (1 - Real.log t) / t ^ 2) (Set.Icc A B) := by
      fun_prop (disch := grind [pow_eq_zero_iff'])
    have hint := (hcont.integrableOn_Icc (μ := volume)).congr_fun (g := deriv F)
       fun t ht => by have ht0 := hA0.trans_le ht.1; simp [F, ht0.ne']  measurableSet_Icc

    -- Step 3: the boundary terms


    have integral_log_div_self : ∫ t in Set.Ioc A B, Real.log t / t =
        (Real.log B ^ 2 - Real.log A ^ 2) / 2 := by
      rw [← intervalIntegral.integral_of_le hAB]
      simpa only [Function.comp_def, id_eq, ← div_eq_mul_inv, integral_id] using
        intervalIntegral.integral_comp_mul_deriv (a := A) (b := B) (g := id)
          (fun x hx => Real.hasDerivAt_log (by grind [Set.uIcc_of_le]))
          (by rw [Set.uIcc_of_le hAB]; fun_prop (disch := grind)) continuous_id
    -- Step 4: the integral
    have hI : - ∫ t in Set.Ioc A B, deriv F t *
          S t ≤
        K * ((Real.log B ^ 2 - Real.log A ^ 2) / 2) := by
      rw [← integral_neg, ← integral_log_div_self, ← integral_const_mul]
      refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc ?_
      · exact ((integrableOn_mul_sum_Icc (m := 0) (sieveNu V) hA0.le hint).mono_set
          Set.Ioc_subset_Icc_self).neg
      · exact ((continuousOn_of_forall_continuousAt fun t ht => (hdiff t ht).continuousAt).integrableOn_Icc.mono_set
          Set.Ioc_subset_Icc_self).const_mul _
      · intro t ht
        have ht0 := hA0.trans ht.1
        have hVt := hVA.trans ht.1.le
        have hlogt := by
          have := Real.log_le_log (Real.exp_pos 1) (hVe.trans hVt)
          rwa [Real.log_exp] at this
        simp [F, ht0.ne']
        have : 0 ≤ S t := by positivity
        have hSK := hSup t hVt
        field_simp; nlinarith
    -- Step 5: the single term
    have hE : F ⌊A⌋₊ * sieveNu V ⌊A⌋₊ ≤
        2 * Real.log A * K := by
      have hm1 := (Nat.one_le_floor_iff A).mpr (by linarith)
      have hm_pos : (0 : ℝ) < ⌊A⌋₊ := by positivity
      have hmA := Nat.floor_le hA0.le
      have hAm := Nat.lt_floor_add_one A
      have hA2m : A ≤ 2 * ⌊A⌋₊ := by linarith
      have hlogm := Real.log_le_log hm_pos hmA
      have hlogm0 : 0 ≤ Real.log ⌊A⌋₊ := Real.log_natCast_nonneg _
      have hlogA0 : 0 ≤ Real.log A := by grind
      have hnu : sieveNu V ⌊A⌋₊ ≤ A * K := by
        refine le_trans ?_ (hSup A hVA)
        exact Finset.single_le_sum (f := fun n => sieveNu V n) (by bound)
           (by bound)

      dsimp only [F]
      rw [div_mul_eq_mul_div, div_le_iff₀ hm_pos]
      nlinarith [mul_le_mul hlogm hA2m hA0.le hlogA0]
    -- Step 6: combine
    dsimp only [ℓ, K, S, F] at *
    linear_combination (norm := (ring_nf; field_simp; nlinarith [sq_nonneg (Real.log B - 1)]))
      step1 +  mul_le_mul_of_nonneg_left (hS B (hVA.trans hAB)).2
        (div_nonneg (by grind : 0 ≤ Real.log B) hB0.le)
        +  mul_le_mul_of_nonneg_left (hS A hVA).1
        (div_nonneg (by grind : 0 ≤ Real.log A) hA0.le)
        + hI + hE +  sum_mul_eq_sub_sub_integral_mul (sieveNu V) hA0.le hAB hdiff hint

end GradedNear
