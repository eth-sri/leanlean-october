/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Tactic

/-!
Uniform prime-weighted reciprocal tails and degree cutoffs.

The Mertens lower bound for the prime sum after excluding a finite
bad-prime set.
-/

@[expose] public section
namespace CCDN
noncomputable section
open Finset Real
open ArithmeticFunction hiding log

/-- The explicit constant in Mertens' first theorem: for every `x ≥ 1`,
`|∑_{p ≤ x} log p / p - log x| ≤ mertensError` (`prime_sum_bounded_error`). -/
def mertensError : ℝ :=
  Real.log 4 + 6 + 4 * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ)

/-- The Mertens error constant `mertensError` is positive. -/
lemma mertensError_pos : 0 < mertensError :=
  add_pos_of_pos_of_nonneg (by positivity)
    (mul_nonneg (by norm_num) (tsum_nonneg fun _ => by positivity))

/-- First Mertens theorem with a coefficient-independent bounded error. -/
theorem prime_sum_bounded_error {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p / p - log x| ≤ mertensError := by
  have h_mangoldt : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    simp_rw [show ∀ n : ℕ, log n = (Λ * zeta) n by simp [vonMangoldt_mul_zeta],
      sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]
  have h_log_le : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x := calc
    _ ≤ ∑ _ ∈ Ioc 0 ⌊x⌋₊, log x := sum_le_sum fun n hn =>
      log_le_log (mod_cast (mem_Ioc.mp hn).1) ((Nat.le_floor_iff (by linarith)).mp (mem_Ioc.mp hn).2)
    _ = ⌊x⌋₊ * log x := by simp
    _ ≤ x * log x := mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (log_nonneg hx)
  have hN (N : ℕ) : (N + 1 : ℝ) * log (N + 1 : ℕ) - N ≤ ∑ n ∈ Ioc 0 (N + 1), log n := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [sum_Ioc_succ_top (Nat.zero_le _)]
      have h1 := mul_le_mul_of_nonneg_right
        (log_le_sub_one_of_pos (by positivity : 0 < (N + 1 + 1 : ℝ) / (N + 1)))
        (by positivity : 0 ≤ (N + 1 : ℝ))
      rw [log_div (by positivity) (by positivity), sub_one_mul,
        div_mul_cancel₀ _ (by positivity)] at h1
      push_cast at ih ⊢
      nlinarith
  have h_log_ge : x * log x - 2 * x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
    have h := hN ⌊x⌋₊
    rw [sum_Ioc_succ_top (Nat.zero_le _), Nat.cast_add, Nat.cast_one] at h
    have hx1 : x * log x ≤ (⌊x⌋₊ + 1 : ℝ) * log (⌊x⌋₊ + 1) :=
      mul_le_mul (Nat.lt_floor_add_one x).le
        (log_le_log (by positivity) (Nat.lt_floor_add_one x).le) (log_nonneg hx) (by positivity)
    linarith [Nat.floor_le (by linarith : 0 ≤ x),
      log_le_sub_one_of_pos (by positivity : 0 < (⌊x⌋₊ + 1 : ℝ))]
  have h_mul_sum : x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]; ring_nf
  have hΛ_ge : log x - 2 ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d := by
    suffices x * (log x - 2) ≤ x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d from
      le_of_mul_le_mul_left this (by linarith)
    calc x * (log x - 2) = x * log x - 2 * x := by ring
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := h_mangoldt ▸ h_log_ge
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
        gcongr; exact Nat.floor_le (div_nonneg (by linarith) (by positivity))
      _ = _ := h_mul_sum.symm
  have hΛ_le : ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ log x + log 4 + 4 := by
    suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) from
      le_of_mul_le_mul_left this (by linarith)
    calc x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := h_mul_sum
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
        gcongr; exact (Nat.lt_floor_add_one _).le
      _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
        simp_rw [mul_add, mul_one, Finset.sum_add_distrib, h_mangoldt]
      _ ≤ x * log x + (log 4 + 4) * x :=
        add_le_add h_log_le (Chebyshev.psi_le_const_mul_self (by linarith))
      _ = _ := by ring
  have hp_le_Λ : ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p / p ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d := by
    rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    · exact div_nonneg vonMangoldt_nonneg (by positivity)
  have hΛ_le_p : ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p / p + 4 * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ) := by
    let N := max 1 ⌊log x / log 2⌋₊
    simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter,
      Chebyshev.sum_PrimePow_eq_sum_sum' _ (by linarith) (le_max_right 1 ⌊log x / log 2⌋₊)]
    calc _ = ∑ k ∈ Icc 1 N, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with p.Prime, log p / (p ^ k : ℕ) :=
        sum_congr rfl fun k hk => sum_congr rfl fun p hp => by
          rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
      _ ≤ ∑ k ∈ Icc 1 N, ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p / (p ^ k : ℕ) := by
        gcongr with k hk
        have hk1 : (1 : ℝ) ≤ k := mod_cast (mem_Icc.mp hk).1
        exact rpow_le_self_of_one_le hx ((div_le_one₀ (by linarith)).mpr hk1)
      _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p / p +
          ∑ k ∈ Ioc 1 N, ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p / (p ^ k : ℕ) := by
        rw [← add_sum_Ioc_eq_sum_Icc (le_max_left 1 _)]; simp; rfl
      _ ≤ _ := by
        gcongr
        rw [sum_comm]
        calc ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, ∑ k ∈ Ioc 1 N, log p / (p ^ k : ℕ)
          _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p * ∑ k ∈ Ico 2 (N + 1), (1 / (p : ℝ)) ^ k :=
            sum_congr rfl fun p _ => by
              rw [mul_sum]; refine sum_congr rfl fun k _ => ?_
              rw [← mul_one_div, Nat.cast_pow, one_div_pow]
          _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, 4 * (p : ℝ) ^ (-3 / 2 : ℝ) := by
            refine sum_le_sum fun p hp => ?_
            have hpP := (mem_filter.mp hp).2
            have hp2 : (2 : ℝ) ≤ p := mod_cast hpP.two_le
            have hp0 : (0 : ℝ) < p := by linarith
            have hgeom : ∑ k ∈ Ico 2 (N + 1), (1 / (p : ℝ)) ^ k ≤ 1 / (p * (p - 1)) := by
              grw [geom_sum_Ico_le_of_lt_one (by positivity)
                (by simpa using inv_lt_one_of_one_lt₀ (mod_cast hpP.one_lt))]
              exact le_of_eq (by field_simp)
            have h1 := Real.log_le_rpow_div hp0.le (by norm_num : (0 : ℝ) < 1 / 2)
            have h2 : (p : ℝ) ^ (1 / 2 : ℝ) = (p : ℝ) ^ (-3 / 2 : ℝ) * p ^ 2 := by
              rw [← rpow_two, ← rpow_add hp0, show (-3 / 2 : ℝ) + 2 = 1 / 2 by norm_num]
            have h3 : 0 ≤ (p : ℝ) ^ (-3 / 2 : ℝ) * (p * (p - 2)) :=
              mul_nonneg (by positivity) (by nlinarith)
            calc log p * ∑ k ∈ Ico 2 (N + 1), (1 / (p : ℝ)) ^ k
              _ ≤ log p * (1 / (p * (p - 1))) := mul_le_mul_of_nonneg_left hgeom (log_natCast_nonneg p)
              _ = log p / (p * (p - 1)) := mul_one_div _ _
              _ ≤ 4 * (p : ℝ) ^ (-3 / 2 : ℝ) :=
                (div_le_iff₀ (by nlinarith)).mpr (by linarith)
          _ ≤ 4 * ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ) := by
            rw [← mul_sum]
            exact mul_le_mul_of_nonneg_left
              ((Real.summable_nat_rpow.mpr (by norm_num)).sum_le_tsum _ fun _ _ => by positivity)
              (by norm_num)
  have hE : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ (-3 / 2 : ℝ) := tsum_nonneg fun _ => by positivity
  have hl : 0 ≤ log 4 := log_nonneg (by norm_num)
  unfold mertensError
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- For `t ≥ 0`, a prime `p` lies in the set of primes in `(0, ⌊t⌋]` if and only if
`p ≤ t`. -/
lemma prime_mem_upto_iff {t : ℝ} (ht : 0 ≤ t) {p : ℕ} (hp : p.Prime) :
    p ∈ ((Ioc 0 ⌊t⌋₊).filter Nat.Prime) ↔ (p : ℝ) ≤ t := by
  simp only [mem_filter, mem_Ioc, hp, and_true, hp.pos, true_and]
  exact Nat.le_floor_iff ht

/-- Mertens bounds an arbitrary prime interval, with its logarithmic width
and two absolute error terms. -/
lemma prime_interval_weight_le {L T : ℝ} (hL : 1 ≤ L) (hLT : L ≤ T)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hlo : ∀ p ∈ P, L < (p : ℝ)) (hhi : ∀ p ∈ P, (p : ℝ) ≤ T) :
    (∑ p ∈ P, Real.log p / p) ≤ Real.log T - Real.log L + 2 * mertensError := by
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  let V := (Ioc 0 ⌊T⌋₊).filter Nat.Prime
  have hUV : U ⊆ V := fun p hp =>
    (prime_mem_upto_iff (by linarith) (mem_filter.mp hp).2).mpr
      (((prime_mem_upto_iff (by linarith) (mem_filter.mp hp).2).mp hp).trans hLT)
  have hPV : P ⊆ V \ U := fun p hp =>
    mem_sdiff.mpr ⟨(prime_mem_upto_iff (by linarith) (hP p hp)).mpr (hhi p hp), fun hu =>
      (not_le_of_gt (hlo p hp)) ((prime_mem_upto_iff (by linarith) (hP p hp)).mp hu)⟩
  have hsum : (∑ p ∈ P, Real.log p / p) ≤ ∑ p ∈ V \ U, Real.log p / p :=
    sum_le_sum_of_subset_of_nonneg hPV fun _ _ _ => by positivity
  have hsplit := sum_sdiff hUV (f := fun p : ℕ => Real.log p / p)
  linarith [(abs_le.mp (prime_sum_bounded_error hL)).1,
    (abs_le.mp (prime_sum_bounded_error (hL.trans hLT))).2]

/-- Lower bound from the first Mertens estimate: for `1 ≤ L ≤ T`, the sum of `log p / p` over the
primes `p` with `L < p ≤ T` is at least `log T - log L - 2 mertensError`. -/
lemma prime_interval_weight_lower {L T : ℝ} (hL : 1 ≤ L) (hLT : L ≤ T) :
    Real.log T - Real.log L - 2 * mertensError ≤
      ∑ p ∈ ((Ioc 0 ⌊T⌋₊).filter Nat.Prime) \ ((Ioc 0 ⌊L⌋₊).filter Nat.Prime),
        Real.log p / p := by
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  let V := (Ioc 0 ⌊T⌋₊).filter Nat.Prime
  have hUV : U ⊆ V := fun p hp =>
    (prime_mem_upto_iff (by linarith) (mem_filter.mp hp).2).mpr
      (((prime_mem_upto_iff (by linarith) (mem_filter.mp hp).2).mp hp).trans hLT)
  have hsplit := sum_sdiff hUV (f := fun p : ℕ => Real.log p / p)
  linarith [(abs_le.mp (prime_sum_bounded_error hL)).2,
    (abs_le.mp (prime_sum_bounded_error (hL.trans hLT))).1]

/-- An explicit constant bounding the prime weight `∑ log p / p` over the primes in any
interval `(L, 4 L]` with `L ≥ 1`. -/
def primeBlockMass : ℝ := Real.log 4 + 2 * mertensError

/-- The prime block constant `primeBlockMass` is positive. -/
lemma primeBlockMass_pos : 0 < primeBlockMass := by
  have h := mertensError_pos
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  dsimp [primeBlockMass]
  linarith

/-- Good-prime reciprocal sum with an explicit lower cutoff. Its error is
O(C/sqrt(L)), with absolute constants, and its small-prime cost is log(L). -/
theorem weighted_prime_sum_lower_cutoff {x L C : ℝ} (hx : 1 ≤ x) (hL : 1 ≤ L)
    (hC : 0 ≤ C) (B : Finset ℕ) (N : ℕ → ℝ)
    (hN : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) → 0 < N p)
    (hupper : ∀ p ∈ ((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B, L < (p : ℝ) →
      N p ≤ p + C * Real.sqrt p) :
    Real.log x - Real.log L - 2 * mertensError - (∑ p ∈ B, Real.log p / p) -
       C * (2 * primeBlockMass / Real.sqrt L) ≤
      ∑ p ∈ (((Ioc 0 ⌊x⌋₊).filter Nat.Prime) \ B).filter (fun p : ℕ => L < (p : ℝ)),
        Real.log p / N p := by
  /- The first Mertens estimate retains an explicit charge for excluded primes. -/
  /- A prime interval above L has weighted reciprocal-square-root mass
  bounded by its Mertens weight divided by sqrt(L). -/
  /- Finite dyadic assembly retains a constant times L^(-1/2), rather than
  summing over every integer and losing a logarithm. -/
  /- The reciprocal-square-root tail over any finite set of primes is uniform
  in its upper endpoint. -/
  /- The exact reciprocal perturbation error, retaining the prime weight
  needed for the sharp tail estimate. -/
  classical
  let T := (Ioc 0 ⌊x⌋₊).filter Nat.Prime
  let U := (Ioc 0 ⌊L⌋₊).filter Nat.Prime
  let S := (T \ B).filter (fun p : ℕ => L < (p : ℝ))
  have hS : S = T \ (B ∪ U) := by
    ext p
    by_cases hp : p ∈ T
    · have hU : p ∈ U ↔ (p : ℝ) ≤ L := prime_mem_upto_iff (by linarith) (mem_filter.mp hp).2
      simp only [S, mem_filter, mem_sdiff, mem_union, hp, true_and, hU, not_or, not_le]
    · simp only [S, mem_filter, mem_sdiff, hp, false_and]
  have hcharge : (∑ p ∈ B ∪ U, Real.log p / p) ≤
      (∑ p ∈ B, Real.log p / p) + (∑ p ∈ U, Real.log p / p) := by
    have he := sum_union_inter (s₁ := B) (s₂ := U) (f := fun p : ℕ => Real.log p / p)
    have hn : 0 ≤ ∑ p ∈ B ∩ U, Real.log p / p := sum_nonneg fun _ _ => by positivity
    linarith
  have hu := (abs_le.mp (prime_sum_bounded_error hL)).2
  have hm : Real.log x - mertensError - (∑ p ∈ B ∪ U, Real.log p / p) ≤
      ∑ p ∈ S, Real.log p / p := by
    rw [hS]
    have hm1 := (abs_le.mp (prime_sum_bounded_error hx)).1
    have he := sum_inter_add_sum_sdiff T (B ∪ U) (fun p : ℕ => Real.log p / p)
    have hB : (∑ p ∈ T ∩ (B ∪ U), Real.log p / p) ≤ ∑ p ∈ B ∪ U, Real.log p / p :=
      sum_le_sum_of_subset_of_nonneg inter_subset_right fun p _ _ => by positivity
    linarith
  have hprime (p : ℕ) (hp : p ∈ S) : p.Prime :=
    (mem_filter.mp (mem_sdiff.mp (mem_filter.mp hp).1).1).2
  have hpow (n : ℕ) {L : ℝ} (hL : 1 ≤ L) (S : Finset ℕ) (hprime : ∀ p ∈ S, p.Prime)
      (hlo : ∀ p ∈ S, L < (p : ℝ)) (hhi : ∀ p ∈ S, (p : ℝ) ≤ 4 ^ n * L) :
      ∑ p ∈ S, Real.log p / p / Real.sqrt p ≤ 2 * primeBlockMass / Real.sqrt L := by
    induction n generalizing L S with
    | zero =>
      have hS0 : S = ∅ := eq_empty_iff_forall_notMem.mpr fun p hp => by
        linarith [hlo p hp, show (p : ℝ) ≤ L by simpa using hhi p hp]
      rw [hS0, sum_empty]
      exact div_nonneg (mul_nonneg (by norm_num) primeBlockMass_pos.le) (Real.sqrt_nonneg _)
    | succ n ih =>
      let A := S.filter (fun p : ℕ => (p : ℝ) ≤ 4 * L)
      have hA : ∑ p ∈ A, Real.log p / p / Real.sqrt p ≤ primeBlockMass / Real.sqrt L := by
        have hle := prime_interval_weight_le hL (by linarith) A
          (fun p hp => hprime p (mem_filter.mp hp).1)
          (fun p hp => hlo p (mem_filter.mp hp).1) (fun _ hp => (mem_filter.mp hp).2)
        rw [Real.log_mul (by norm_num) (by linarith)] at hle
        calc ∑ p ∈ A, Real.log p / p / Real.sqrt p
          _ ≤ (∑ p ∈ A, Real.log p / p) / Real.sqrt L := by
            rw [sum_div]
            exact sum_le_sum fun p hp => div_le_div_of_nonneg_left (by positivity)
              (Real.sqrt_pos.mpr (by linarith))
              (Real.sqrt_le_sqrt (hlo p (mem_filter.mp hp).1).le)
          _ ≤ primeBlockMass / Real.sqrt L :=
            div_le_div_of_nonneg_right (by dsimp [primeBlockMass]; linarith) (Real.sqrt_nonneg L)
      have hB := ih (L := 4 * L) (by linarith) (S \ A)
        (fun p hp => hprime p (mem_sdiff.mp hp).1)
        (fun p hp => by
          have hm := mem_sdiff.mp hp
          exact lt_of_not_ge (by simpa only [A, mem_filter, hm.1, true_and] using hm.2))
        (fun p hp => by simpa only [pow_succ, mul_assoc] using hhi p (mem_sdiff.mp hp).1)
      rw [← sum_sdiff (filter_subset (fun p : ℕ => (p : ℝ) ≤ 4 * L) S)]
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by norm_num] at hB
      have hL0 : Real.sqrt L ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
      calc _ ≤ 2 * primeBlockMass / (2 * Real.sqrt L) + primeBlockMass / Real.sqrt L :=
            add_le_add hB hA
           _ = _ := by field_simp; ring
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (((S.sup id : ℕ) : ℝ) / L) (by norm_num : (1 : ℝ) < 4)
  have htail := hpow n hL S hprime (fun _ hp => (mem_filter.mp hp).2) fun p hp =>
    (Nat.cast_le.mpr (le_sup (f := id) hp)).trans ((div_lt_iff₀ (by linarith)).mp hn).le
  have hs : ∑ p ∈ S, (Real.log p / p - C * (Real.log p / p / Real.sqrt p)) ≤
      ∑ p ∈ S, Real.log p / N p :=
    sum_le_sum fun p hp => by
      have hp1 : (1 : ℝ) ≤ p := mod_cast (hprime p hp).one_le
      have hp0 : (0 : ℝ) < p := by linarith
      have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
      have hsq : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
      have hrec : 1 / (p : ℝ) - C / (p * Real.sqrt p) ≤ 1 / (p + C * Real.sqrt p) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < p + C * Real.sqrt p)).mpr
        field_simp; nlinarith [sq_nonneg C]
      calc Real.log p / p - C * (Real.log p / p / Real.sqrt p)
        _ = Real.log p * (1 / p - C / (p * Real.sqrt p)) := by ring
        _ ≤ Real.log p * (1 / (p + C * Real.sqrt p)) :=
          mul_le_mul_of_nonneg_left hrec (Real.log_nonneg hp1)
        _ ≤ Real.log p / N p := by
          rw [mul_one_div]
          exact div_le_div_of_nonneg_left (Real.log_nonneg hp1)
            (hN p (mem_filter.mp hp).1 (mem_filter.mp hp).2)
            (hupper p (mem_filter.mp hp).1 (mem_filter.mp hp).2)
  rw [sum_sub_distrib, ← mul_sum] at hs
  nlinarith

end
end CCDN
