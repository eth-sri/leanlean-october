/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! A fixed exponential in the number of distinct prime factors is
subpower. The proof splits the prime divisors at a fixed cutoff; above
the cutoff, each logarithmic cost is absorbed by the prime itself. -/

public section
namespace CCDN
open Finset

private theorem primeFactors_sum_log_le {D : ℕ} (hD : 1 ≤ D) :
    ∑ p ∈ D.primeFactors, Real.log ↑p ≤ Real.log ↑D := by
  have hprod : (∏ p ∈ D.primeFactors, (p : ℝ)) ≤ D := by
    rw [← Nat.cast_prod]
    exact Nat.cast_le.mpr (Nat.le_of_dvd (by omega : 0 < D) (Nat.prod_primeFactors_dvd D))
  have hpos : ∀ p ∈ D.primeFactors, (0 : ℝ) < p := fun p hp =>
    Nat.cast_pos.mpr (Nat.prime_of_mem_primeFactors hp).pos
  rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
  exact Real.log_le_log (prod_pos hpos) hprod

/-- The constant is chosen before the integer whose prime divisors are
counted. This form also permits a real exponential base. -/
private theorem primeFactors_pow_subpower {R ε : ℝ} (hR : 1 ≤ R) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
      R ^ D.primeFactors.card ≤ C * ↑D ^ ε := by
  have hR0 := zero_lt_one.trans_le hR
  have hlogR := Real.log_nonneg hR
  obtain ⟨M, hM⟩ := exists_nat_gt (Real.exp (Real.log R / ε))
  have hM0 := (Real.exp_pos _).trans hM
  have hcut := by
    have hh := Real.log_le_log (Real.exp_pos _) hM.le
    rw [Real.log_exp] at hh
    have hh := (div_le_iff₀ hε).mp hh
    simpa only [mul_comm] using hh
  refine ⟨Real.exp (↑M * Real.log R), Real.exp_pos _, ?_⟩
  intro D hD
  have hD0 : (0 : ℝ) < D := by positivity
  have hsmall : (D.primeFactors.filter (· < M)).card ≤ M := by
    exact Trans.trans (card_le_card fun p hp => mem_range.mpr (mem_filter.mp hp).right) (card_range M)
  have hterm : ∀ p ∈ D.primeFactors,
      Real.log R ≤ (if p < M then Real.log R else 0) + ε * Real.log ↑p := by
    intro p hp
    have hp1 : 1 ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    by_cases hpm : p < M
    · simp_all [   Real.log_nonneg]
    · rw [ite_eq_right hpm, zero_add]
      exact hcut.trans (mul_le_mul_of_nonneg_left
        (Real.log_le_log hM0 (by simp_all)) hε.le)
  have hsum : ↑D.primeFactors.card * Real.log R ≤
      ↑M * Real.log R + ε * Real.log ↑D := by
    calc
      _ = ∑ _p ∈ D.primeFactors, Real.log R := by simp
      _ ≤ ∑ p ∈ D.primeFactors,
          ((if p < M then Real.log R else 0) + ε * Real.log ↑p) :=
        sum_le_sum hterm
      _ = (D.primeFactors.filter (· < M)).card * Real.log R +
          ε * ∑ p ∈ D.primeFactors, Real.log ↑p := by
        rw [sum_add_distrib, ← sum_filter, ← mul_sum]
        simp
      _ ≤ _ := add_le_add
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hsmall) hlogR)
        (mul_le_mul_of_nonneg_left (primeFactors_sum_log_le hD) hε.le)
  have hexp := Real.exp_le_exp.mpr hsum
  rw [← Real.log_pow, Real.exp_log (pow_pos hR0 _)] at hexp
  convert hexp using 1
  rw [Real.rpow_def_of_pos hD0, ← Real.exp_add]
  congr 1
  ring

/-- For every `a` and `ε > 0` there is `C > 0` with `2 ^ (a * ω(D)) ≤ C * D ^ ε` for all `D ≥ 1`,
where `ω(D)` is the number of distinct prime factors of `D`. -/
theorem two_pow_primeFactors_subpower (a : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D →
      2 ^ (a * D.primeFactors.card) ≤ C * ↑D ^ ε := by
  simp_all [primeFactors_pow_subpower, one_le_pow₀, pow_mul]

end CCDN
