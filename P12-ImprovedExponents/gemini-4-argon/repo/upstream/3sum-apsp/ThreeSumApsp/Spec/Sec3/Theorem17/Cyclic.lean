module

public import ThreeSumApsp.Util.Log
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.NumberTheory.Bertrand
public import PaperStatements
public import ThreeSumApsp.Util.Index
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.RingTheory.AdjoinRoot
public import ThreeSumApsp.Util.List

@[expose] public section

open Finset

namespace Nat

/-- The primes `p` with `n < p ≤ 2n`: the primes that Bertrand's postulate is about. -/
def bertrandPrimes (n : ℕ) : Finset ℕ := (Ioc n (2 * n)).filter Nat.Prime

/-- Membership in `bertrandPrimes`, spelled out. -/
theorem mem_bertrandPrimes {n p : ℕ} :
    p ∈ bertrandPrimes n ↔ (n < p ∧ p ≤ 2 * n) ∧ p.Prime := by
  simp only [bertrandPrimes, mem_filter, mem_Ioc]

/-! ## 1. Erdős's upper bound for the central binomial coefficient -/

/-- Every prime power in `C(2n, n)` is at most `2n`, so `|s|` of them multiply to at most
`(2n)^|s|`. -/
theorem prod_pow_factorization_le {n : ℕ} (hn : 0 < n) (s : Finset ℕ) :
    ∏ p ∈ s, p ^ n.centralBinom.factorization p ≤ (2 * n) ^ s.card :=
  prod_le_pow_card _ _ _ fun _ _ => Nat.pow_factorization_choose_le (by omega)

/-- The primes in `(√(2n), n]` contribute at most `4^(2n/3)` to `C(2n, n)`: their exponent is at
most 1, it is 0 above `2n/3`, and the product of the primes up to `2n/3` is at most `4^(2n/3)`.
Adapted from Mathlib, Mathlib/NumberTheory/Bertrand.lean, Apache 2.0. -/
theorem prod_middle_le {n : ℕ} (hn : 2 < n) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ Nat.sqrt (2 * n) < p ∧ p ≤ n) :
    ∏ p ∈ s, p ^ n.centralBinom.factorization p ≤ 4 ^ (2 * n / 3) :=
  calc ∏ p ∈ s, p ^ n.centralBinom.factorization p
      ≤ ∏ p ∈ s, (if p ≤ 2 * n / 3 then p else 1) := by
        refine prod_le_prod' fun p hp => ?_
        obtain ⟨hprime, hsqrt, hpn⟩ := hs p hp
        split_ifs with h3
        · exact (pow_right_mono₀ hprime.one_lt.le
            (Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp hsqrt))).trans (pow_one p).le
        · rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn hpn (by omega),
            pow_zero]
    _ = ∏ p ∈ s.filter (· ≤ 2 * n / 3), p := (prod_filter _ _).symm
    _ ≤ primorial (2 * n / 3) := by
        refine prod_le_prod_of_subset_of_one_le' (fun p hp => ?_)
          fun p hp _ => (mem_filter.1 hp).2.one_lt.le
        obtain ⟨hps, hp3⟩ := mem_filter.1 hp
        exact mem_filter.2 ⟨mem_range.2 (by omega), (hs p hps).1⟩
    _ ≤ 4 ^ (2 * n / 3) := primorial_le_four_pow _

/-- Erdős's bound, keeping the primes of `(n, 2n]`:
`C(2n, n) ≤ (2n)^√(2n) · 4^(2n/3) · (2n)^k`, where `k` is the number of primes in `(n, 2n]`.
Mathlib proves the case `k = 0` on the way to Bertrand's postulate
(`centralBinom_le_of_no_bertrand_prime`).  Adapted from Mathlib, Mathlib/NumberTheory/Bertrand.lean,
Apache 2.0. -/
theorem centralBinom_le (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) * (2 * n) ^ (bertrandPrimes n).card := by
  -- `C(2n, n)` is the product of its prime powers over the set `T` of the primes up to `2n`.
  set T := (range (2 * n + 1)).filter Nat.Prime with hT
  have hprod : ∏ p ∈ T, p ^ n.centralBinom.factorization p = n.centralBinom :=
    (prod_filter_of_ne fun p _ h => by
      contrapose h
      rw [Nat.factorization_eq_zero_of_not_prime _ h, pow_zero]).trans
      n.prod_pow_factorization_centralBinom
  -- Split the primes at `n`, and those up to `n` at `√(2n)`.
  rw [← hprod, ← prod_filter_mul_prod_filter_not T (· ≤ n),
    ← prod_filter_mul_prod_filter_not (T.filter (· ≤ n)) (· ≤ Nat.sqrt (2 * n))]
  refine mul_le_mul' (mul_le_mul' ?_ ?_) ?_
  · -- There are at most `√(2n)` primes up to `√(2n)`.
    have hsub : (T.filter (· ≤ n)).filter (· ≤ Nat.sqrt (2 * n)) ⊆ Icc 1 (Nat.sqrt (2 * n)) := by
      intro p hp
      simp only [hT, mem_filter, mem_range] at hp
      obtain ⟨⟨⟨-, hprime⟩, -⟩, hsqrt⟩ := hp
      exact mem_Icc.mpr ⟨hprime.one_lt.le, hsqrt⟩
    exact (prod_pow_factorization_le (by omega) _).trans (pow_right_mono₀ (by omega)
      ((card_le_card hsub).trans_eq (by rw [Nat.card_Icc, Nat.add_sub_cancel])))
  · -- The primes in `(√(2n), n]`.
    refine prod_middle_le hn _ fun p hp => ?_
    simp only [hT, mem_filter, mem_range, not_le] at hp
    obtain ⟨⟨⟨-, hprime⟩, hpn⟩, hsqrt⟩ := hp
    exact ⟨hprime, hsqrt, hpn⟩
  · -- The primes above `n` are those of `(n, 2n]`.
    refine (prod_pow_factorization_le (by omega) _).trans
      (pow_right_mono₀ (by omega) (card_le_card fun p hp => ?_))
    simp only [hT, mem_filter, mem_range] at hp
    obtain ⟨⟨hp2n, hprime⟩, hnp⟩ := hp
    exact mem_bertrandPrimes.2 ⟨⟨by omega, by omega⟩, hprime⟩

/-! ## 2. The elementary estimate `n^6 · (2n)^(6√(2n)) ≤ 2^n` for `n ≥ 16562` -/

/-- For `a ≥ 0` the function `log x + √(2x) · log (2x) - a x` is concave for `x > 1/2`.
Adapted from Mathlib, Mathlib/NumberTheory/Bertrand.lean, Apache 2.0 (there inside
`Bertrand.real_main_inequality`, for `a = log 4 / 3`). -/
theorem concaveOn_log_add_sqrt_mul_log_sub (a : ℝ) (ha : 0 ≤ a) :
    ConcaveOn ℝ (Set.Ioi (1 / 2 : ℝ))
    (fun x : ℝ => Real.log x + √(2 * x) * Real.log (2 * x) - a * x) := by
  apply ConcaveOn.sub
  · apply ConcaveOn.add
    · exact strictConcaveOn_log_Ioi.concaveOn.subset
        (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi _)
    · have h := strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
        ((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
      have hset : (⇑((2 : ℝ) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))) ⁻¹' Set.Ioi 1 = Set.Ioi (1 / 2) := by
        ext x
        simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
          smul_eq_mul]
        constructor <;> intro h <;> linarith
      rw [hset] at h
      exact h
  · exact ConvexOn.smul ha (convexOn_id (convex_Ioi _))

/-- `log x + √(2x) · log (2x) ≤ (log 2 / 6) · x` for `x ≥ 16562`.  The difference of the two sides
is concave, it is nonnegative at `x = 2` and nonpositive at `x = 16562 = 2 · 91²` (where
`√(2x) = 182`; the only numerical input is `91^13 ≤ 2^85`), so it is nonpositive from there on.
Adapted from Mathlib, Mathlib/NumberTheory/Bertrand.lean, Apache 2.0 (the same argument proves
`Bertrand.real_main_inequality` there, with other numbers). -/
theorem log_add_sqrt_mul_log_le {x : ℝ} (hx : 16562 ≤ x) :
    Real.log x + √(2 * x) * Real.log (2 * x) ≤ Real.log 2 / 6 * x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hat2 : (0 : ℝ) ≤
      Real.log 2 + √(2 * 2) * Real.log (2 * 2) - Real.log 2 / 6 * 2 := by
    rw [Real.sqrt_mul_self (by norm_num), Real.log_mul (by norm_num) (by norm_num)]
    linarith
  have hat16562 : Real.log 16562 + √(2 * 16562) * Real.log (2 * 16562)
      - Real.log 2 / 6 * 16562 ≤ 0 := by
    have hlog91 : 13 * Real.log 91 ≤ 85 * Real.log 2 := by
      have h := Real.log_le_log (by positivity) (show (91 : ℝ) ^ 13 ≤ 2 ^ 85 by norm_num)
      rw [Real.log_pow, Real.log_pow] at h
      exact_mod_cast h
    have hlogx : Real.log 16562 = Real.log 2 + 2 * Real.log 91 := by
      rw [show (16562 : ℝ) = 2 * 91 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]
      norm_num
    have hlog2x : Real.log (182 * 182) = 2 * Real.log 2 + 2 * Real.log 91 := by
      rw [show (182 * 182 : ℝ) = 2 ^ 2 * 91 ^ 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
      norm_num
    rw [show (2 * 16562 : ℝ) = 182 * 182 by norm_num, Real.sqrt_mul_self (by norm_num), hlogx,
      hlog2x]
    -- `366 log 91 ≤ 366 · (85/13) log 2 < (16562/6 - 365) log 2`
    linarith only [hlog91, hlog2]
  have hconcave := concaveOn_log_add_sqrt_mul_log_sub (Real.log 2 / 6) (by positivity)
  have hatx := hconcave.right_le_of_le_left''
    (x := 2) (y := 16562) (z := x) (by norm_num [Set.mem_Ioi]) (by rw [Set.mem_Ioi]; linarith)
    (by norm_num) hx (hat16562.trans hat2)
  linarith only [hatx, hat16562]

/-- The same estimate for natural numbers, without logarithms. -/
theorem pow_mul_pow_sqrt_le_two_pow {n : ℕ} (hn : 16562 ≤ n) :
    n ^ 6 * (2 * n) ^ (6 * Nat.sqrt (2 * n)) ≤ 2 ^ n := by
  have hx : (16562 : ℝ) ≤ n := by exact_mod_cast hn
  have hreal := log_add_sqrt_mul_log_le hx
  have hsqrt : (Nat.sqrt (2 * n) : ℝ) ≤ √(2 * n) := by
    exact_mod_cast Real.nat_sqrt_le_real_sqrt (a := 2 * n)
  have hlog : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have : (0 : ℝ) < n := by linarith
  rw [← Nat.cast_le (α := ℝ)]
  push_cast
  rw [← Real.log_le_log_iff (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
  push_cast
  -- `6 log n + 6 ⌊√(2n)⌋ log(2n) ≤ 6 (log n + √(2n) log(2n)) ≤ n log 2`
  linarith [hreal, mul_le_mul_of_nonneg_right hsqrt hlog]

/-! ## 3. The count for `n ≥ 16562` -/

/-- `2^n ≤ (2n)^(2k)` for `n ≥ 16562`.  If it failed, the sixth power of
`4^n < n · (2n)^√(2n) · 4^(2n/3) · (2n)^k` would give
`2^(12n) < (n^6 (2n)^(6√(2n))) · 2^(8n) · 2^(3n) ≤ 2^(12n)`. -/
theorem two_pow_le_of_large {n : ℕ} (hn : 16562 ≤ n) :
    2 ^ n ≤ (2 * n) ^ (2 * (bertrandPrimes n).card) := by
  by_contra hcon
  have hfew : (2 * n) ^ (2 * (bertrandPrimes n).card) ≤ 2 ^ n := (not_le.mp hcon).le
  have herdos : 4 ^ n < n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)
      * (2 * n) ^ (bertrandPrimes n).card) :=
    (Nat.four_pow_lt_mul_centralBinom n (by omega)).trans_le
      (Nat.mul_le_mul_left _ (centralBinom_le n (by omega)))
  have hsmall := pow_mul_pow_sqrt_le_two_pow hn
  have hmiddle : 4 ^ (6 * (2 * n / 3)) ≤ 4 ^ (4 * n) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  refine lt_irrefl ((4 ^ n) ^ 6) ?_
  calc (4 ^ n) ^ 6
      < (n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)
          * (2 * n) ^ (bertrandPrimes n).card)) ^ 6 := Nat.pow_lt_pow_left herdos (by norm_num)
    _ = (n ^ 6 * (2 * n) ^ (6 * Nat.sqrt (2 * n))) * 4 ^ (6 * (2 * n / 3))
          * ((2 * n) ^ (2 * (bertrandPrimes n).card)) ^ 3 := by ring
    _ ≤ 2 ^ n * 4 ^ (4 * n) * (2 ^ n) ^ 3 := by gcongr
    _ = (4 ^ n) ^ 6 := by
        rw [mul_comm 4 n, pow_mul 4 n 4, show (4 : ℕ) ^ n = 2 ^ n * 2 ^ n by rw [← mul_pow]; rfl]
        ring

/-- The count of step 3 with natural logarithms: `n log 2 ≤ 2 k log (2n)`. -/
theorem mul_log_two_le_card_bertrandPrimes_mul_log {n : ℕ} (hn : 16562 ≤ n) :
    (n : ℝ) * Real.log 2 ≤ 2 * (bertrandPrimes n).card * Real.log (2 * n) := by
  have hpow : (2 : ℝ) ^ n ≤ (2 * (n : ℝ)) ^ (2 * (bertrandPrimes n).card) := by
    exact_mod_cast two_pow_le_of_large hn
  have hlog := Real.log_le_log (by positivity) hpow
  rw [Real.log_pow, Real.log_pow] at hlog
  exact_mod_cast hlog

/-! ## 4. Half-open windows `[x/2, x)` with real endpoints -/

/-- For a real `x ≥ 4` the natural number `n = ⌈x/2⌉ - 1`, written below as `(⌈x⌉ - 1) / 2`,
satisfies `n ≥ 1`, `n ≥ x/4` and `2n < x`, and every natural number in `(n, 2n]` lies in `[x/2, x)`.
-/
theorem exists_nat_window {x : ℝ} (hx : 4 ≤ x) :
    ∃ n : ℕ, 1 ≤ n ∧ x / 4 ≤ (n : ℝ) ∧ 2 * (n : ℝ) < x ∧
      ∀ p : ℕ, n < p → p ≤ 2 * n → x / 2 ≤ (p : ℝ) ∧ (p : ℝ) < x := by
  have hle : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
  have : 4 ≤ ⌈x⌉₊ := by exact_mod_cast hx.trans hle
  obtain ⟨n, hn⟩ : ∃ n, n = (⌈x⌉₊ - 1) / 2 := ⟨_, rfl⟩
  have : (⌈x⌉₊ : ℝ) ≤ 2 * n + 2 := by exact_mod_cast (by omega : ⌈x⌉₊ ≤ 2 * n + 2)
  have : (2 * n + 1 : ℝ) ≤ (⌈x⌉₊ : ℝ) := by exact_mod_cast (by omega : 2 * n + 1 ≤ ⌈x⌉₊)
  refine ⟨n, by omega, by linarith, by linarith, fun p hnp hp2n => ?_⟩
  have : (n : ℝ) + 1 ≤ p := by exact_mod_cast hnp
  have : (p : ℝ) ≤ 2 * n := by exact_mod_cast hp2n
  exact ⟨by linarith, by linarith⟩

/-- For every real `x ≥ 4` there is a prime `p` with `x/2 ≤ p < x`, by Bertrand's postulate. -/
theorem exists_prime_half_le_and_lt (x : ℝ) (hx : 4 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x / 2 ≤ (p : ℝ) ∧ (p : ℝ) < x := by
  obtain ⟨n, hn1, -, -, hwindow⟩ := exists_nat_window hx
  obtain ⟨p, hprime, hnp, hp2n⟩ := Nat.exists_prime_lt_and_le_two_mul n (by omega)
  exact ⟨p, hprime, hwindow p hnp hp2n⟩

/-- If `(n, 2n]` lies in the window and `n ≥ x/4` is large, the window has at least `x / (12 log x)`
primes: `(x/4) log 2 ≤ n log 2 ≤ 2 k log (2n) ≤ 2 k log x`, and `log 2 ≥ 2/3`. -/
theorem div_log_le_card_of_large {x : ℝ} {n : ℕ} {S : Finset ℕ} (hx : 4 ≤ x)
    (hn : 16562 ≤ n) (hn4 : x / 4 ≤ (n : ℝ)) (h2n : 2 * (n : ℝ) < x) (hsub : bertrandPrimes n ⊆ S) :
    x / (12 * Real.log x) ≤ (S.card : ℝ) := by
  have : ((bertrandPrimes n).card : ℝ) ≤ S.card := by exact_mod_cast card_le_card hsub
  have : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have : Real.log (2 * n) ≤ Real.log x := Real.log_le_log (by linarith) h2n.le
  have : 0 ≤ Real.log (2 * n) := Real.log_nonneg (by linarith)
  have : 2 / 3 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  rw [div_le_iff₀ (mul_pos (by norm_num) (Real.log_pos (by linarith)))]
  calc x = 6 * (x / 4 * (2 / 3)) := by ring
    _ ≤ 6 * (n * Real.log 2) := by gcongr
    _ ≤ 6 * (2 * (bertrandPrimes n).card * Real.log (2 * n)) :=
        mul_le_mul_of_nonneg_left (mul_log_two_le_card_bertrandPrimes_mul_log hn) (by norm_num)
    _ ≤ 6 * (2 * S.card * Real.log x) := by gcongr
    _ = S.card * (12 * Real.log x) := by ring

/-- There is a `c > 0` such that, for every real `x ≥ 4`, every finite set of natural numbers that
contains all primes `p` with `x/2 ≤ p < x` has at least `c · x / log x` elements.  (This form
applies to the set of those primes however it is written down.) -/
theorem exists_forall_mul_div_log_le_card_primes :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ℝ, 4 ≤ x → ∀ S : Finset ℕ,
      (∀ p : ℕ, p.Prime → x / 2 ≤ (p : ℝ) → (p : ℝ) < x → p ∈ S) →
      c * (x / Real.log x) ≤ (S.card : ℝ) := by
  -- `66248 = 4 · 16562`: for `x` below it one prime is enough
  refine ⟨1 / 66248, by norm_num, fun x hx S hS => ?_⟩
  obtain ⟨n, hn1, hn4, h2n, hwindow⟩ := exists_nat_window hx
  have : 1 ≤ Real.log x := Real.one_le_log_of_three_le (by linarith)
  rcases le_or_gt 16562 n with hlarge | hsmall
  · -- The primes of `(n, 2n]` lie in the window.
    have hsub : bertrandPrimes n ⊆ S := fun p hp => by
      obtain ⟨⟨hnp, hp2n⟩, hprime⟩ := mem_bertrandPrimes.1 hp
      exact hS p hprime (hwindow p hnp hp2n).1 (hwindow p hnp hp2n).2
    calc 1 / 66248 * (x / Real.log x) ≤ 1 / 12 * (x / Real.log x) := by gcongr; norm_num
      _ = x / (12 * Real.log x) := by field_simp
      _ ≤ (S.card : ℝ) := div_log_le_card_of_large hx hlarge hn4 h2n hsub
  · -- Here `x ≤ 4n < 66248`, and one prime is enough.
    obtain ⟨p, hprime, hlow, hhigh⟩ := exists_prime_half_le_and_lt x hx
    have hone : (1 : ℝ) ≤ S.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨p, hS p hprime hlow hhigh⟩
    have : (n : ℝ) ≤ 16562 := by exact_mod_cast hsmall.le
    calc 1 / 66248 * (x / Real.log x) ≤ 1 / 66248 * (x / 1) := by gcongr
      _ ≤ 1 := by linarith
      _ ≤ (S.card : ℝ) := hone

/-! ## 5. The window `[√D/2, √D)` of the proof of Theorem 17 -/

/-- Proof of Theorem 17: "there are Ω(√D / log D) primes in the range".  There is a `c > 0` such
that, for every natural number `D ≥ 16`, every finite set of natural numbers that contains all
primes `p` with `√D/2 ≤ p < √D` has at least `c · √D / log D` elements. -/
theorem exists_forall_mul_sqrt_div_log_le_card_primes :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 16 ≤ D → ∀ S : Finset ℕ,
      (∀ p : ℕ, p.Prime → √D / 2 ≤ (p : ℝ) → (p : ℝ) < √D → p ∈ S) →
      c * (√D / Real.log D) ≤ (S.card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := exists_forall_mul_div_log_le_card_primes
  refine ⟨c, hc, fun D hD S hS => ?_⟩
  have : 0 < Real.log D := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  calc c * (√D / Real.log D) ≤ c * (√D / (Real.log D / 2)) := by
        gcongr
        linarith
    _ = c * (√D / Real.log (√D)) := by rw [Real.log_sqrt (Nat.cast_nonneg D)]
    _ ≤ (S.card : ℝ) := hcount _ (Real.four_le_sqrt_natCast_of_sixteen_le hD) S hS

end Nat

namespace ThreeSumApsp

/-! ### The primes in the range -/

/-- Proof of Theorem 17, "a prime p ∈ [√D/2, √D)": the primes in the range are the primes `p` with
`√D/2 ≤ p < √D`.  (The bound `p < D` in the definition excludes none of them.) -/
theorem mem_primesInRange {D p : ℕ} :
    p ∈ primesInRange D ↔ p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℝ) < Real.sqrt D := by
  unfold primesInRange
  rw [Finset.mem_filter, Finset.mem_range]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  -- From `p < √D` we get `p ≤ p² < D`.
  have hsq : p ^ 2 < D := by exact_mod_cast (Real.lt_sqrt (Nat.cast_nonneg p)).1 h.2.2
  exact (Nat.le_self_pow two_ne_zero p).trans_lt hsq

/-! ### The ring `ℤ[x]/(x^p − 1)` -/

open Polynomial in
/-- Proof of Theorem 17: "the ring ℤ[x]/(x^p − 1)".  (`Polynomial.C 1` is the constant polynomial
1.) -/
abbrev CyclicRing (p : ℕ) : Type := AdjoinRoot ((X : ℤ[X]) ^ p - C 1)

namespace CyclicRing

open Polynomial

variable {p : ℕ}

/-- The element `x` of `ℤ[x]/(x^p − 1)`. -/
noncomputable def x (p : ℕ) : CyclicRing p := AdjoinRoot.root _

/-- Proof of Theorem 17: "the coefficient of x^r" in an element `z` of `ℤ[x]/(x^p − 1)`, for `0 ≤ r
< p`, as a linear map: the coefficient of `x^r` in the unique polynomial of degree less than `p`
that represents `z` (Mathlib's `AdjoinRoot.modByMonicHom` gives that polynomial; it asks for the
fact that `x^p − 1` is monic, which holds as `p ≠ 0`). -/
noncomputable def coeff (hp : p ≠ 0) (r : ℕ) : CyclicRing p →ₗ[ℤ] ℤ :=
  lcoeff ℤ r ∘ₗ AdjoinRoot.modByMonicHom (monic_X_pow_sub_C (1 : ℤ) hp)

/-- The coefficient, in terms of the representing polynomial. -/
theorem coeff_apply (hp : p ≠ 0) (r : ℕ) (z : CyclicRing p) :
    coeff hp r z = (AdjoinRoot.modByMonicHom (monic_X_pow_sub_C (1 : ℤ) hp) z).coeff r :=
  rfl

/-- In `ℤ[x]/(x^p − 1)` we have `x^p = 1`. -/
theorem x_pow_self (p : ℕ) : x p ^ p = 1 := by
  have h : AdjoinRoot.mk ((X : ℤ[X]) ^ p - C 1) ((X : ℤ[X]) ^ p - C 1) = 0 := AdjoinRoot.mk_self
  rw [map_sub, map_pow, AdjoinRoot.mk_X, C_1, map_one] at h
  exact sub_eq_zero.1 h

/-- The coefficient of `x^r` in the power `x^k` of `ℤ[x]/(x^p − 1)` is 1 if `r = k mod p` and 0
otherwise. -/
theorem coeff_x_pow (hp : p ≠ 0) (k r : ℕ) :
    coeff hp r (x p ^ k) = if r = k % p then 1 else 0 := by
  have hred : x p ^ k = x p ^ (k % p) := by
    conv_lhs => rw [← Nat.div_add_mod k p, pow_add, pow_mul, x_pow_self, one_pow, one_mul]
  have hdeg : ((X : ℤ[X]) ^ (k % p)).degree < ((X : ℤ[X]) ^ p - C 1).degree := by
    rw [degree_X_pow, degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
    exact_mod_cast Nat.mod_lt k (Nat.pos_of_ne_zero hp)
  rw [coeff_apply, hred, x, ← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (monic_X_pow_sub_C (1 : ℤ) hp)).2 hdeg, coeff_X_pow]

end CyclicRing

/-- A number `r < p` is the sum of the residues of `u` and `v` in `{0, …, p − 1}`, reduced modulo
`p`, exactly if `u + v ≡ r`. -/
theorem eq_add_toNat_emod_iff {p r : ℕ} (hp : p ≠ 0) (hr : r < p) (u v : ℤ) :
    r = ((u % (p : ℤ)).toNat + (v % (p : ℤ)).toNat) % p ↔ u + v ≡ (r : ℤ) [ZMOD (p : ℤ)] := by
  rw [← Int.natCast_inj, Int.ModEq, Int.emod_eq_of_lt (Int.natCast_nonneg r) (by exact_mod_cast hr),
    eq_comm]
  push_cast
  rw [Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp),
    Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp),
    ← Int.add_emod]

/-! ### Counting the triples with `S(a,b,c) ≡ 0 (mod p)` -/

namespace TriangleInstance

variable {n : ℕ} (T : TriangleInstance ℤ n)

/-- Proof of Theorem 17: "A false positive of p is a triple (a,b,c) with S(a,b,c) ≠ 0 and p ∣
S(a,b,c)". -/
def IsFalsePositive (p : ℕ) (t : Fin n × Fin n × Fin n) : Prop :=
  T.S t.1 t.2.1 t.2.2 ≠ 0 ∧ (p : ℤ) ∣ T.S t.1 t.2.1 t.2.2

open Classical in
/-- Proof of Theorem 17: "let F(p) denote the number of false positives of p". -/
noncomputable def F (p : ℕ) : ℕ :=
  (Finset.univ.filter fun t : Fin n × Fin n × Fin n => T.IsFalsePositive p t).card

open Classical in
/-- Proof of Theorem 17: "Z₀, the number of zero triangles". -/
noncomputable def Z₀ : ℕ :=
  (Finset.univ.filter fun t : Fin n × Fin n × Fin n => T.IsZeroTriangle t.1 t.2.1 t.2.2).card

/-- Proof of Theorem 17: "This number is the number of false positives F(p) plus Z₀, the number of
zero triangles, which does not depend on p." -/
theorem countZeroMod_eq (p : ℕ) : T.countZeroMod p = T.F p + T.Z₀ := by
  classical
  simp only [countZeroMod, F, Z₀, Finset.card_filter, ← Finset.sum_add_distrib]
  -- A triple with `p ∣ S(a,b,c)` is a zero triangle or a false positive, and not both.
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases h0 : T.S t.1 t.2.1 t.2.2 = 0 <;>
    simp [IsFalsePositive, IsZeroTriangle, Int.modEq_zero_iff_dvd, h0]

/-- Proof of Theorem 17: "let P[a,c] := x^{w(a,c) mod p}", a matrix over `ℤ[x]/(x^p − 1)`.  `w mod
p` is the residue in `{0, …, p − 1}`. -/
noncomputable def matP (p : ℕ) : Matrix (Fin n) (Fin n) (CyclicRing p) :=
  Matrix.of fun a c => CyclicRing.x p ^ (T.wAC a c % (p : ℤ)).toNat

/-- Proof of Theorem 17: "and Q[c,b] := x^{w(b,c) mod p}". -/
noncomputable def matQ (p : ℕ) : Matrix (Fin n) (Fin n) (CyclicRing p) :=
  Matrix.of fun c b => CyclicRing.x p ^ (T.wBC b c % (p : ℤ)).toNat

/-- Proof of Theorem 17: "the coefficient of x^r in (PQ)[a,b] is the number of c ∈ C with w(a,c) +
w(b,c) ≡ r (mod p)". -/
theorem coeff_matP_mul_matQ {p : ℕ} (hp : p ≠ 0) (a b : Fin n) (r : ℕ) (hr : r < p) :
    CyclicRing.coeff hp r ((T.matP p * T.matQ p) a b) =
      ((Finset.univ.filter fun c : Fin n =>
        T.wAC a c + T.wBC b c ≡ (r : ℤ) [ZMOD (p : ℤ)]).card : ℤ) := by
  classical
  -- `(PQ)[a,b]` is the sum over `c` of `x^(w(a,c) mod p + w(b,c) mod p)`, and the coefficient of
  -- `x^r` in each term is 1 or 0.
  rw [Matrix.mul_apply]
  simp only [matP, matQ, Matrix.of_apply, ← pow_add]
  rw [map_sum]
  simp only [CyclicRing.coeff_x_pow]
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [eq_add_toNat_emod_iff hp hr]

/-- Proof of Theorem 17: "then F(p) + Z₀ is the sum over the pairs (a,b) ∈ A × B of the coefficient
of x^{−w(a,b) mod p} in (PQ)[a,b]". -/
theorem F_add_Z₀_eq_sum_coeff {p : ℕ} (hp : p ≠ 0) :
    ((T.F p + T.Z₀ : ℕ) : ℤ) =
      ∑ a : Fin n, ∑ b : Fin n,
        CyclicRing.coeff hp ((-T.wAB a b) % (p : ℤ)).toNat ((T.matP p * T.matQ p) a b) := by
  classical
  rw [← countZeroMod_eq]
  unfold countZeroMod
  rw [Finset.card_filter, Fintype.sum_prod_type]
  push_cast
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hcast := Int.natCast_toNat_emod (Nat.pos_of_ne_zero hp) (-T.wAB a b)
  rw [T.coeff_matP_mul_matQ hp a b _ (Int.toNat_emod_lt (Nat.pos_of_ne_zero hp) _),
    Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  -- `S(a,b,c) ≡ 0` says the same as `w(a,c) + w(b,c) ≡ -w(a,b)`, and `-w(a,b)` is congruent to its
  -- residue.
  have hres : (-T.wAB a b) % (p : ℤ) ≡ -T.wAB a b [ZMOD (p : ℤ)] := Int.mod_modEq _ _
  have hiff : T.S a b c ≡ 0 [ZMOD (p : ℤ)] ↔
      T.wAC a c + T.wBC b c ≡ ((((-T.wAB a b) % (p : ℤ)).toNat : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
    rw [hcast, show T.wAC a c + T.wBC b c ≡ (-T.wAB a b) % (p : ℤ) [ZMOD (p : ℤ)] ↔
        T.wAC a c + T.wBC b c ≡ -T.wAB a b [ZMOD (p : ℤ)] from
      ⟨fun h => h.trans hres, fun h => h.trans hres.symm⟩,
      Int.modEq_iff_dvd, Int.modEq_iff_dvd,
      show 0 - T.S a b c = -T.wAB a b - (T.wAC a c + T.wBC b c) by
        simp only [S]; ring]
  simp only [hiff]


/-! ### Selecting the prime -/


variable {n D p : ℕ} {κ : ℝ} (T : TriangleInstance ℤ n)

/-- Proof of Theorem 17.  There is a prime to select. -/
theorem exists_isSelectedPrime (D : ℕ) (hD : 16 ≤ D) : ∃ p, T.IsSelectedPrime D p := by
  obtain ⟨q, hq⟩ :=
    Nat.exists_prime_half_le_and_lt (Real.sqrt D) (Real.four_le_sqrt_natCast_of_sixteen_le hD)
  exact Finset.exists_min_image (primesInRange D) T.countZeroMod ⟨q, mem_primesInRange.2 hq⟩

/-- Proof of Theorem 17: "We select the prime with the smallest count, which is also the prime with
the fewest false positives". -/
theorem IsSelectedPrime.F_le {T : TriangleInstance ℤ n} (hp : T.IsSelectedPrime D p) :
    ∀ q ∈ primesInRange D, T.F p ≤ T.F q := by
  intro q hq
  have h := hp.2 q hq
  rw [countZeroMod_eq, countZeroMod_eq] at h
  omega

/-! ### The bound on the number of false positives of the selected prime -/

/-- Proof of Theorem 17: "|S(a,b,c)| ≤ 3n^ν". -/
theorem abs_S_le (hT : T.WeightsPolyBounded κ) (a b c : Fin n) :
    ((|T.S a b c| : ℤ) : ℝ) ≤ 3 * (n : ℝ) ^ κ := by
  obtain ⟨hAB, hBC, hAC⟩ := hT
  have habs : |T.S a b c| ≤ |T.wAB a b| + |T.wBC b c| + |T.wAC a c| := abs_add_three _ _ _
  have : ((|T.S a b c| : ℤ) : ℝ)
      ≤ ((|T.wAB a b| : ℤ) : ℝ) + ((|T.wBC b c| : ℤ) : ℝ) + ((|T.wAC a c| : ℤ) : ℝ) := by
    exact_mod_cast habs
  linarith [hAB a b, hBC b c, hAC a c]

open Classical in
/-- Proof of Theorem 17: "a triple with S(a,b,c) ≠ 0 is a false positive exactly of the primes in
the range that divide S(a,b,c).  Since 0 < |S(a,b,c)| ≤ 3n^ν and these primes are at least √D/2,
there are at most log_{√D/2}(3n^ν) of them." -/
theorem card_falsePositive_primes_le (hD : 16 ≤ D) (hT : T.WeightsPolyBounded κ)
    (t : Fin n × Fin n × Fin n) (ht : T.S t.1 t.2.1 t.2.2 ≠ 0) :
    (((primesInRange D).filter fun p => T.IsFalsePositive p t).card : ℝ)
      ≤ Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
  have := Real.four_le_sqrt_natCast_of_sixteen_le hD
  set divisors := (primesInRange D).filter fun p => T.IsFalsePositive p t
  have hmem : ∀ p ∈ divisors,
      p.Prime ∧ Real.sqrt D / 2 ≤ (p : ℝ) ∧ (p : ℤ) ∣ T.S t.1 t.2.1 t.2.2 := by
    intro p hp
    obtain ⟨hrange, -, hdvd⟩ := Finset.mem_filter.1 hp
    obtain ⟨hprime, hge, -⟩ := mem_primesInRange.1 hrange
    exact ⟨hprime, hge, hdvd⟩
  -- The product of these primes divides `S(a,b,c)`, so it is at most `|S(a,b,c)| ≤ 3n^κ`.
  have hdvd : ∏ p ∈ divisors, p ∣ (T.S t.1 t.2.1 t.2.2).natAbs :=
    Finset.prod_primes_dvd _ (fun p hp => (hmem p hp).1.prime)
      fun p hp => Int.natCast_dvd.1 (hmem p hp).2.2
  have hprod : ∏ p ∈ divisors, (p : ℝ) ≤ 3 * (n : ℝ) ^ κ :=
    calc ∏ p ∈ divisors, (p : ℝ) = ((∏ p ∈ divisors, p : ℕ) : ℝ) := (Nat.cast_prod _ _).symm
      _ ≤ ((T.S t.1 t.2.1 t.2.2).natAbs : ℝ) := by
          exact_mod_cast Nat.le_of_dvd (Int.natAbs_pos.2 ht) hdvd
      _ = ((|T.S t.1 t.2.1 t.2.2| : ℤ) : ℝ) := Nat.cast_natAbs _
      _ ≤ 3 * (n : ℝ) ^ κ := T.abs_S_le hT _ _ _
  -- Each of these primes is at least `√D/2`.
  have hpow : (Real.sqrt D / 2) ^ divisors.card ≤ ∏ p ∈ divisors, (p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => by linarith) fun p hp => (hmem p hp).2.1
  have hY : 0 < 3 * (n : ℝ) ^ κ := lt_of_lt_of_le (by positivity) (hpow.trans hprod)
  rw [Real.le_logb_iff_rpow_le (by linarith) hY, Real.rpow_natCast]
  exact hpow.trans hprod

/-- Proof of Theorem 17: "Hence the numbers of false positives of all the primes in the range add up
to at most n³ log_{√D/2}(3n^ν)." -/
theorem sum_F_le (hD : 16 ≤ D) (hκ : 1 ≤ κ) (hT : T.WeightsPolyBounded κ) :
    ((∑ p ∈ primesInRange D, T.F p : ℕ) : ℝ)
      ≤ (n : ℝ) ^ 3 * Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
  classical
  have hsqrt := Real.four_le_sqrt_natCast_of_sixteen_le hD
  -- Count the pairs (prime, false positive of that prime) triple by triple.
  have hswap : ∑ p ∈ primesInRange D, T.F p = ∑ t : Fin n × Fin n × Fin n,
      ((primesInRange D).filter fun p => T.IsFalsePositive p t).card := by
    simp only [F, Finset.card_filter]
    exact Finset.sum_comm
  have hterm : ∀ t : Fin n × Fin n × Fin n,
      (((primesInRange D).filter fun p => T.IsFalsePositive p t).card : ℝ)
        ≤ Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
    intro t
    by_cases ht : T.S t.1 t.2.1 t.2.2 = 0
    · -- A zero triangle is a false positive of no prime.
      rw [Finset.filter_eq_empty_iff.2 fun p _ h => h.1 ht, Finset.card_empty, Nat.cast_zero]
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast Fin.pos t.1
      have hpow : (1 : ℝ) ≤ (n : ℝ) ^ κ := Real.one_le_rpow hn (by linarith)
      exact Real.logb_nonneg (by linarith) (by linarith)
    · -- Otherwise this is the bound of `card_falsePositive_primes_le` for this triple.
      convert T.card_falsePositive_primes_le hD hT t ht
  rw [hswap, Nat.cast_sum]
  calc ∑ t : Fin n × Fin n × Fin n,
        (((primesInRange D).filter fun p => T.IsFalsePositive p t).card : ℝ)
      ≤ ∑ _t : Fin n × Fin n × Fin n, Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) :=
        Finset.sum_le_sum fun t _ => hterm t
    _ = (n : ℝ) ^ 3 * Real.logb (Real.sqrt D / 2) (3 * (n : ℝ) ^ κ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_prod,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end TriangleInstance

/-- Proof of Theorem 17: "By the prime number theorem there are Ω(√D/log D) primes in the range".

NOTE.  The proof of Theorem 17 needs this for every `D ≥ 16`, not only for large `D`, and so it is
stated.  It follows from a counting form of Bertrand's postulate; the prime number theorem is not
needed. -/
theorem exists_le_card_primesInRange :
    ∃ c : ℝ, 0 < c ∧ ∀ D : ℕ, 16 ≤ D →
      c * (Real.sqrt D / Real.log D) ≤ ((primesInRange D).card : ℝ) := by
  obtain ⟨c, hc, hcount⟩ := Nat.exists_forall_mul_sqrt_div_log_le_card_primes
  exact ⟨c, hc, fun D hD => hcount D hD _
    fun _ hp hge hlt => mem_primesInRange.2 ⟨hp, hge, hlt⟩⟩

/-- Proof of Theorem 17: "F(p) is at most the average over them", multiplied out. -/
theorem TriangleInstance.IsSelectedPrime.F_mul_card_le_sum {n D p : ℕ} {T : TriangleInstance ℤ n}
    (hp : T.IsSelectedPrime D p) :
    T.F p * (primesInRange D).card ≤ ∑ q ∈ primesInRange D, T.F q := by
  rw [mul_comm, ← smul_eq_mul]
  exact Finset.card_nsmul_le_sum _ _ _ hp.F_le

/-- Proof of Theorem 17: "log D = O(log(√D/2)) for D ≥ 16". -/
theorem log_le_four_mul_log_sqrt_div_two (D : ℕ) (hD : 16 ≤ D) :
    Real.log D ≤ 4 * Real.log (Real.sqrt D / 2) := by
  have : (16 : ℝ) ≤ D := by exact_mod_cast hD
  have hsqrt : 0 < Real.sqrt D := by linarith [Real.four_le_sqrt_natCast_of_sixteen_le hD]
  -- `log(√D/2) = (log D)/2 - log 2`, and `4 log 2 = log 16 ≤ log D`.
  have hlog16 : 4 * Real.log 2 ≤ Real.log D := by
    have h := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 4 ≤ D by linarith)
    rw [Real.log_pow] at h
    exact_mod_cast h
  rw [Real.log_div hsqrt.ne' (by norm_num), Real.log_sqrt (by linarith)]
  linarith [hlog16]

/-- Proof of Theorem 17: "F(p) is at most the average over them, so [...] F(p) = O(n³
log(3n^ν)/√D)": if there are at least `c √D/log D` primes in the range, then `F(p) ≤ (4/c) n³
log(3n^κ)/√D`. -/
theorem TriangleInstance.F_le_of_le_card_primesInRange {n D p : ℕ} {κ c : ℝ}
    (T : TriangleInstance ℤ n) (hc : 0 < c)
    (hcard : c * (Real.sqrt D / Real.log D) ≤ ((primesInRange D).card : ℝ)) (hD : 16 ≤ D)
    (hDn : D ≤ n) (hκ : 1 ≤ κ) (hT : T.WeightsPolyBounded κ) (hp : T.IsSelectedPrime D p) :
    (T.F p : ℝ) ≤ 4 / c * ((n : ℝ) ^ 3 * Real.log (3 * (n : ℝ) ^ κ) / Real.sqrt D) := by
  -- The quantities of the paper's sentence: `r = √D`, `Y = 3n^κ`, and the number of primes in the
  -- range.
  set r := Real.sqrt D
  set Y := 3 * (n : ℝ) ^ κ with hY
  set numPrimes := (primesInRange D).card
  have hr : 4 ≤ r := Real.four_le_sqrt_natCast_of_sixteen_le hD
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  have hlogD_pos : 0 < Real.log D := Real.log_pos (by exact_mod_cast (by omega : 1 < D))
  have hlogr_pos : 0 < Real.log (r / 2) := Real.log_pos (by linarith)
  have hlogY_nonneg : 0 ≤ Real.log Y := by
    have : 1 ≤ (n : ℝ) ^ κ := Real.one_le_rpow (by linarith) (by linarith)
    exact Real.log_nonneg (by rw [hY]; linarith)
  -- "F(p) is at most the average", multiplied out; the false positives of all the primes in the
  -- range add up to at most `n³ log_{r/2} Y`.
  have average : (T.F p : ℝ) * numPrimes ≤ (n : ℝ) ^ 3 * Real.logb (r / 2) Y :=
    le_trans (by exact_mod_cast hp.F_mul_card_le_sum) (T.sum_F_le hD hκ hT)
  -- The base of the logarithm changes: `log_{r/2} Y ≤ 4 log Y / log D`.
  have hlogD_le : Real.log D ≤ 4 * Real.log (r / 2) := log_le_four_mul_log_sqrt_div_two D hD
  have changeBase : Real.logb (r / 2) Y ≤ 4 * Real.log Y / Real.log D := by
    rw [Real.logb, div_le_div_iff₀ hlogr_pos hlogD_pos]
    linarith [mul_le_mul_of_nonneg_left hlogD_le hlogY_nonneg]
  rw [show 4 / c * ((n : ℝ) ^ 3 * Real.log Y / r) = 4 * (n : ℝ) ^ 3 * Real.log Y / (c * r) by
    field_simp, le_div_iff₀ (by positivity)]
  calc (T.F p : ℝ) * (c * r) = T.F p * (c * (r / Real.log D)) * Real.log D := by field_simp
    _ ≤ T.F p * numPrimes * Real.log D := by gcongr
    _ ≤ (n : ℝ) ^ 3 * Real.logb (r / 2) Y * Real.log D := by gcongr
    _ ≤ (n : ℝ) ^ 3 * (4 * Real.log Y / Real.log D) * Real.log D := by gcongr
    _ = 4 * (n : ℝ) ^ 3 * Real.log Y := by field_simp

/-- Proof of Theorem 17: "F(p) = O(n³ log(3n^ν)/√D) = O(ν n³ log n/√D)". -/
theorem TriangleInstance.exists_F_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {n D p : ℕ} {κ : ℝ}, 16 ≤ D → D ≤ n → 1 ≤ κ → ∀ T : TriangleInstance ℤ n,
      T.WeightsPolyBounded κ → T.IsSelectedPrime D p →
      (T.F p : ℝ) ≤ C * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) := by
  obtain ⟨c, hc, hcard⟩ := exists_le_card_primesInRange
  refine ⟨max 1 (8 / c), le_max_left _ _, fun {n D p κ} hD hDn hκ T hT hp => ?_⟩
  have hn : (16 : ℝ) ≤ n := by exact_mod_cast hD.trans hDn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  -- `log(3n^κ) = log 3 + κ log n ≤ 2κ log n`, because `3 ≤ n` and `κ ≥ 1`.
  have hlog : Real.log (3 * (n : ℝ) ^ κ) ≤ 2 * κ * Real.log n := by
    have hlog3 : Real.log 3 ≤ κ * Real.log n :=
      (Real.log_le_log (by norm_num) (by linarith)).trans (le_mul_of_one_le_left hlogn hκ)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow (by linarith)]
    linarith [hlog3]
  calc (T.F p : ℝ) ≤ 4 / c * ((n : ℝ) ^ 3 * Real.log (3 * (n : ℝ) ^ κ) / Real.sqrt D) :=
        T.F_le_of_le_card_primesInRange hc (hcard D hD) hD hDn hκ hT hp
    _ ≤ 4 / c * ((n : ℝ) ^ 3 * (2 * κ * Real.log n) / Real.sqrt D) := by gcongr
    _ = 8 / c * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) := by ring
    _ ≤ max 1 (8 / c) * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) := by
        gcongr
        exact le_max_right _ _

/-- A name for the constant in "F(p) = [...] = O(ν n³ log n/√D)", for the bounds on running times
that are built on this one. -/
noncomputable def Hashing.falsePositiveConst : ℝ := Classical.choose TriangleInstance.exists_F_le

/-- The constant is at least 1. -/
theorem Hashing.one_le_falsePositiveConst : 1 ≤ Hashing.falsePositiveConst :=
  (Classical.choose_spec TriangleInstance.exists_F_le).1

/-- Proof of Theorem 17: "F(p) = [...] = O(ν n³ log n/√D)", with `Hashing.falsePositiveConst` as the
constant. -/
theorem Hashing.F_le_falsePositiveConst_mul {n D p : ℕ} {κ : ℝ} (hD : 16 ≤ D) (hDn : D ≤ n)
    (hκ : 1 ≤ κ) (T : TriangleInstance ℤ n) (hT : T.WeightsPolyBounded κ)
    (hp : T.IsSelectedPrime D p) :
    (T.F p : ℝ) ≤ Hashing.falsePositiveConst * (κ * (n : ℝ) ^ 3 * Real.log n / Real.sqrt D) :=
  (Classical.choose_spec TriangleInstance.exists_F_le).2 hD hDn hκ T hT hp

end ThreeSumApsp

namespace ThreeSumApsp.Spec

/-- An element of `ℤ[x]/(x^p − 1)` as the list of its coefficients of `x^0, …, x^{p-1}`. -/
noncomputable def cycVec {p : ℕ} (hp : p ≠ 0) (z : CyclicRing p) : List ℤ :=
  (List.range p).map fun r => CyclicRing.coeff hp r z

/-- Entrywise sum. -/
def vadd (u v : List ℤ) : List ℤ := List.zipWith (· + ·) u v

/-- Entrywise difference. -/
def vsub (u v : List ℤ) : List ℤ := List.zipWith (· - ·) u v

/-- The vector of `x^k`, for `k < p`. -/
def vunit (p k : ℕ) : List ℤ := (List.range p).map fun i => if i = k then 1 else 0

/-- Cyclic convolution: entry `r` is the sum of `u_i v_j` over `i + j ≡ r (mod p)`.  The index `j`
is `r - i` or `r + p - i`. -/
def cconv (p : ℕ) (u v : List ℤ) : List ℤ :=
  (List.range p).map fun r =>
    ((List.range p).map fun i => u.getD i 0 * v.getD (if i ≤ r then r - i else r + p - i) 0).sum

variable {p : ℕ} (hp : p ≠ 0)

/-! ## Coefficients -/

/-- The representative of degree less than `p` has no coefficients from `p` on. -/
theorem coeff_eq_zero_of_le (z : CyclicRing p) {r : ℕ} (hr : p ≤ r) :
    CyclicRing.coeff hp r z = 0 := by
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective z
  rw [CyclicRing.coeff_apply, AdjoinRoot.modByMonicHom_mk]
  refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le
    (Polynomial.degree_modByMonic_lt f (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp)) ?_)
  rw [Polynomial.degree_X_pow_sub_C (Nat.pos_of_ne_zero hp)]
  exact_mod_cast hr

/-- An element of the ring is the combination of the powers of `x` with its coefficients. -/
theorem eq_sum_coeff (z : CyclicRing p) :
    z = ∑ i ∈ Finset.range p, CyclicRing.coeff hp i z • CyclicRing.x p ^ i := by
  have hmk := AdjoinRoot.mk_leftInverse (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp) z
  set f := AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow_sub_C (1 : ℤ) hp) z with hf
  have hdeg : f.natDegree < p := by
    by_contra hc
    have hlead : f.coeff f.natDegree = 0 := coeff_eq_zero_of_le hp z (not_lt.mp hc)
    rw [Polynomial.leadingCoeff_eq_zero.mp hlead, Polynomial.natDegree_zero] at hc
    exact hc (Nat.pos_of_ne_zero hp)
  conv_lhs => rw [← hmk, Polynomial.as_sum_range' f p hdeg, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    zsmul_eq_mul]
  simp [CyclicRing.coeff_apply, CyclicRing.x, hf]

/-- For `i, j, r < p`: `i + j ≡ r (mod p)` exactly if `j` is `r - i` or `r + p - i`. -/
theorem eq_add_mod_iff {p i j r : ℕ} (hi : i < p) (hj : j < p) (hr : r < p) :
    r = (i + j) % p ↔ j = if i ≤ r then r - i else r + p - i := by
  by_cases h : i + j < p
  · rw [Nat.mod_eq_of_lt h]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (not_lt.mp h), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega

/-! ## Vectors -/

/-- A vector has `p` entries. -/
theorem length_cycVec (z : CyclicRing p) : (cycVec hp z).length = p := by
  simp [cycVec]

/-- Entry `r` of the vector is the coefficient of `x^r`. -/
theorem getD_cycVec (z : CyclicRing p) {r : ℕ} (hr : r < p) :
    (cycVec hp z).getD r 0 = CyclicRing.coeff hp r z :=
  List.getD_map_range _ hr 0

/-- The vector of 0. -/
theorem cycVec_zero : cycVec hp 0 = List.replicate p 0 := by
  rw [cycVec, List.eq_replicate_iff]
  refine ⟨by simp, fun b hb => ?_⟩
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hb
  exact map_zero (CyclicRing.coeff hp r)

/-- The vector of a sum. -/
theorem cycVec_add (z w : CyclicRing p) :
    cycVec hp (z + w) = vadd (cycVec hp z) (cycVec hp w) := by
  refine List.ext_getElem (by simp [vadd, length_cycVec]) fun r _ _ => ?_
  simp only [vadd, cycVec, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  exact map_add (CyclicRing.coeff hp r) z w

/-- The vector of a difference. -/
theorem cycVec_sub (z w : CyclicRing p) :
    cycVec hp (z - w) = vsub (cycVec hp z) (cycVec hp w) := by
  refine List.ext_getElem (by simp [vsub, length_cycVec]) fun r _ _ => ?_
  simp only [vsub, cycVec, List.getElem_zipWith, List.getElem_map, List.getElem_range]
  exact map_sub (CyclicRing.coeff hp r) z w

/-- The vector of a power of `x`. -/
theorem cycVec_x_pow (k : ℕ) : cycVec hp (CyclicRing.x p ^ k) = vunit p (k % p) :=
  List.map_congr_left fun r _ => CyclicRing.coeff_x_pow hp k r

/-- Multiplication in the ring is cyclic convolution. -/
theorem cycVec_mul (z w : CyclicRing p) :
    cycVec hp (z * w) = cconv p (cycVec hp z) (cycVec hp w) := by
  refine List.map_congr_left fun r hr => ?_
  have hr' := List.mem_range.mp hr
  -- Expand both factors in powers of x.
  conv_lhs => rw [eq_sum_coeff hp z, eq_sum_coeff hp w, Finset.sum_mul_sum]
  rw [map_sum, List.sum_map_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  have := Finset.mem_range.mp hi
  -- For each i, only one j contributes to the coefficient of x^r.
  have hj : (if i ≤ r then r - i else r + p - i) < p := by split_ifs <;> omega
  rw [getD_cycVec hp z this, getD_cycVec hp w hj, map_sum]
  simp only [smul_mul_smul_comm, ← pow_add, map_zsmul, CyclicRing.coeff_x_pow, smul_eq_mul]
  rw [Finset.sum_eq_single (if i ≤ r then r - i else r + p - i)]
  · rw [if_pos ((eq_add_mod_iff this hj hr').mpr rfl), mul_one]
  · intro j hj' hne
    rw [if_neg fun h => hne ((eq_add_mod_iff this (Finset.mem_range.mp hj') hr').mp h), mul_zero]
  · exact fun h => absurd (Finset.mem_range.mpr hj) h

end ThreeSumApsp.Spec
