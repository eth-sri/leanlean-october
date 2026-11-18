module

public import Erdos408.Basic
public import Mathlib.NumberTheory.Bertrand
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Mertens' theorems on intervals

Elementary calculus-free proofs of `∑_{p ≤ x} log p / p = log x + O(1)` and
`∑_{y < p ≤ z} 1 / p = log (log z / log y) + O(1 / log y)`, which are all the
prime-distribution input the deduction needs besides Chebyshev's upper bound
for `π(x)`.
-/

@[expose] public section

namespace Erdos408

open Finset Real
open ArithmeticFunction hiding log

private lemma prod_Ioc_zero_eq_factorial : ∀ n : ℕ, (∏ k ∈ Ioc 0 n, k) = n.factorial
  | 0 => rfl
  | n + 1 => by
    rw [prod_Ioc_succ_top (Nat.zero_le n), prod_Ioc_zero_eq_factorial n, Nat.factorial_succ,
      mul_comm]

lemma sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    x * Real.log x - 2 * x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n := by
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.floor_pos.mpr hx
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x - 1 < N := Nat.sub_one_lt_floor x
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hfact : (N : ℝ) ^ N / (N.factorial : ℝ) ≤ Real.exp N :=
    Real.pow_div_factorial_le_exp (N : ℝ) hNpos.le N
  have hprod : (N.factorial : ℝ) = ∏ n ∈ Ioc 0 N, (n : ℝ) := by
    rw [← prod_Ioc_zero_eq_factorial N, Nat.cast_prod]
  have hfpos : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have hlog_fact : Real.log ((N : ℝ) ^ N / (N.factorial : ℝ)) ≤ N := by
    calc Real.log ((N : ℝ) ^ N / (N.factorial : ℝ))
        ≤ Real.log (Real.exp N) := Real.log_le_log (div_pos (pow_pos hNpos N) hfpos) hfact
      _ = N := Real.log_exp N
  rw [Real.log_div (pow_pos hNpos N).ne' hfpos.ne', Real.log_pow, hprod,
    Real.log_prod fun n hn => by exact_mod_cast (mem_Ioc.mp hn).1.ne'] at hlog_fact
  have hd1 : (x - N) * Real.log x ≤ Real.log x :=
    mul_le_of_le_one_left (Real.log_nonneg hx) (by linarith)
  have hd2 : (N : ℝ) * (Real.log x - Real.log N) ≤ x - N := by
    rw [← Real.log_div (by linarith) hNpos.ne']
    have := Real.log_le_sub_one_of_pos (div_pos (show 0 < x by linarith) hNpos)
    nlinarith [div_mul_cancel₀ x hNpos.ne']
  have hlx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  nlinarith

theorem sum_mangoldt_div_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d - Real.log x| ≤ Real.log 4 + 4 := by
  have hm : ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    have h1 : ∀ n : ℕ, Real.log n = (Λ * zeta) n := fun n => by simp [vonMangoldt_mul_zeta]
    simp_rw [h1, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]
  have hlo : -2 ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d - Real.log x := by
    suffices x * (Real.log x - 2) ≤ x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d by nlinarith
    calc x * (Real.log x - 2) = x * Real.log x - 2 * x := by ring
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := hm ▸ sum_log_ge hx
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := sum_le_sum fun d _ =>
          mul_le_mul_of_nonneg_left (Nat.floor_le (by positivity)) vonMangoldt_nonneg
      _ = x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d := by rw [mul_sum]; refine sum_congr rfl fun _ _ => by ring
  have hhi : ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d - Real.log x ≤ Real.log 4 + 4 := by
    suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (Real.log x + Real.log 4 + 4) by nlinarith
    have hlog_le : ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n ≤ x * Real.log x := by
      calc ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n
          ≤ ∑ _ ∈ Ioc 0 ⌊x⌋₊, Real.log x := sum_le_sum fun n hn =>
            Real.log_le_log (by exact_mod_cast (mem_Ioc.mp hn).1)
              ((Nat.le_floor_iff (by linarith)).mp (mem_Ioc.mp hn).2)
        _ = ⌊x⌋₊ * Real.log x := by simp
        _ ≤ x * Real.log x :=
            mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith)) (Real.log_nonneg hx)
    calc x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d
        = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
            rw [mul_sum]; refine sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := sum_le_sum fun d _ =>
          mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one _).le vonMangoldt_nonneg
      _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Real.log n + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
          simp_rw [mul_add, mul_one, sum_add_distrib, ← hm]
      _ ≤ x * Real.log x + (Real.log 4 + 4) * x :=
          add_le_add hlog_le (Chebyshev.psi_le_const_mul_self (by linarith))
      _ = x * (Real.log x + Real.log 4 + 4) := by ring
  rw [abs_le]
  have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  exact ⟨by linarith, hhi⟩

private lemma sum_Ico_sub (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ k ∈ Ico a b, (f (k + 1) - f k) = f b - f a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [sum_Ico_succ_top hm, ih]; ring

lemma sum_inv_mul_sqrt_le (N : ℕ) :
    ∑ n ∈ Icc 2 N, 1 / ((n : ℝ) * √(n : ℝ)) ≤ 2 := by
  have hstrong : ∀ M : ℕ, 1 ≤ M →
      ∑ n ∈ Icc 2 M, 1 / ((n : ℝ) * √(n : ℝ)) ≤ 2 - 2 / √(M : ℝ) := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => simp
    | succ m hm ih =>
      rw [sum_Icc_succ_top (by omega)]
      have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
      have hsm : 0 < √(m : ℝ) := Real.sqrt_pos.mpr (by linarith)
      have hsm1 : 0 < √((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have hle : √(m : ℝ) ≤ √((m + 1 : ℕ) : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ m)
      have hsq : √(m : ℝ) ^ 2 = m := Real.sq_sqrt (by positivity)
      have hsq1 : √((m + 1 : ℕ) : ℝ) ^ 2 = (m + 1 : ℕ) := Real.sq_sqrt (by positivity)
      have hstep : 1 / (((m + 1 : ℕ) : ℝ) * √((m + 1 : ℕ) : ℝ)) ≤
          2 / √(m : ℝ) - 2 / √((m + 1 : ℕ) : ℝ) := by
        rw [div_sub_div _ _ hsm.ne' hsm1.ne', div_le_div_iff₀ (by positivity) (mul_pos hsm hsm1)]
        have : (√((m + 1 : ℕ) : ℝ) - √(m : ℝ)) * (√((m + 1 : ℕ) : ℝ) + √(m : ℝ)) = 1 := by
          push_cast at hsq1 ⊢; nlinarith
        nlinarith [mul_nonneg hsm.le (sub_nonneg.mpr hle)]
      linarith
  rcases eq_zero_or_pos N with rfl | hN
  · simp
  · linarith [hstrong N hN, show 0 ≤ 2 / √(N : ℝ) by positivity]

private lemma sum_log_prime_div_sub_log_le {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p - Real.log x| ≤ Real.log 4 + 12 := by
  have hle : ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d := by
    rw [sum_filter]
    refine sum_le_sum fun d _ => ?_
    split_ifs with hd
    · rw [vonMangoldt_apply_prime hd]
    · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hpp : ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤
      ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p + 8 := by
    have hcp := Chebyshev.sum_PrimePow_eq_sum_sum (fun d => Λ d / d) (x := (⌊x⌋₊ : ℝ)) (by positivity)
    rw [Nat.floor_natCast] at hcp
    have hlhs : ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d = ∑ d ∈ Ioc 0 ⌊x⌋₊ with IsPrimePow d, Λ d / d := by
      rw [sum_filter]
      refine sum_congr rfl fun d _ => ?_
      by_cases hd : IsPrimePow d
      · simp [hd]
      · simp [hd, vonMangoldt_eq_zero_iff.mpr hd]
    rw [hlhs, hcp]
    set K := max 1 ⌊Real.log (⌊x⌋₊ : ℝ) / Real.log 2⌋₊
    calc ∑ k ∈ Icc 1 ⌊Real.log (⌊x⌋₊ : ℝ) / Real.log 2⌋₊,
          ∑ p ∈ Ioc 0 ⌊(⌊x⌋₊ : ℝ) ^ (1 / (k : ℝ))⌋₊ with p.Prime, Λ (p ^ k) / ↑(p ^ k)
        = ∑ k ∈ Icc 1 ⌊Real.log (⌊x⌋₊ : ℝ) / Real.log 2⌋₊,
          ∑ p ∈ Ioc 0 ⌊(⌊x⌋₊ : ℝ) ^ (1 / (k : ℝ))⌋₊ with p.Prime, Real.log p / (p : ℝ) ^ k := by
          refine sum_congr rfl fun k hk => sum_congr rfl fun p hp => ?_
          rw [vonMangoldt_apply_pow (by have := (mem_Icc.mp hk).1; omega),
            vonMangoldt_apply_prime (mem_filter.mp hp).2, Nat.cast_pow]
      _ ≤ ∑ k ∈ Icc 1 K, ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / (p : ℝ) ^ k := by
          refine (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (le_max_right _ _))
            fun _ _ _ => sum_nonneg fun _ _ => by positivity).trans (sum_le_sum fun k hk => ?_)
          refine sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ (Ioc_subset_Ioc_right ?_))
            fun _ _ _ => by positivity
          have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hx
          have hk1 : 1 / (k : ℝ) ≤ 1 :=
            div_le_one_of_le₀ (by exact_mod_cast (mem_Icc.mp hk).1) (by positivity)
          exact Nat.floor_le_of_le (Real.rpow_le_self_of_one_le h1 hk1)
      _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p +
          ∑ k ∈ Ioc 1 K, ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / (p : ℝ) ^ k := by
          rw [← add_sum_Ioc_eq_sum_Icc (le_max_left 1 _)]; congr 1; simp
      _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, Real.log p / p + 8 := by
          gcongr
          rw [sum_comm]
          calc ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, ∑ k ∈ Ioc 1 K, Real.log p / (p : ℝ) ^ k
              ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, 4 * (1 / ((p : ℝ) * √(p : ℝ))) := by
                refine sum_le_sum fun p hp => ?_
                have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.two_le
                have hgeom : ∑ k ∈ Ioc 1 K, Real.log p / (p : ℝ) ^ k ≤
                    2 * Real.log p / (p : ℝ) ^ 2 := by
                  have hIoc : Ioc 1 K = Ico 2 (K + 1) := rfl
                  have hstep : ∀ k ∈ Ico 2 (K + 1), (1 / (p : ℝ)) ^ k ≤
                      2 * ((1 / (p : ℝ)) ^ k - (1 / (p : ℝ)) ^ (k + 1)) := by
                    intro k _
                    have hr0 : 0 ≤ (1 / (p : ℝ)) ^ k := by positivity
                    have hr2 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
                    rw [pow_succ]; nlinarith
                  have htel := sum_Ico_sub (fun k => -((1 / (p : ℝ)) ^ k))
                    (a := 2) (b := K + 1) (by omega)
                  simp only [neg_sub_neg] at htel
                  have hlhs' : ∑ k ∈ Ioc 1 K, Real.log p / (p : ℝ) ^ k =
                      Real.log p * ∑ k ∈ Ico 2 (K + 1), (1 / (p : ℝ)) ^ k := by
                    rw [hIoc, mul_sum]; refine sum_congr rfl fun k _ => by rw [one_div_pow]; ring
                  rw [hlhs']
                  calc Real.log p * ∑ k ∈ Ico 2 (K + 1), (1 / (p : ℝ)) ^ k
                      ≤ Real.log p * ∑ k ∈ Ico 2 (K + 1),
                          2 * ((1 / (p : ℝ)) ^ k - (1 / (p : ℝ)) ^ (k + 1)) :=
                        mul_le_mul_of_nonneg_left (sum_le_sum hstep) (Real.log_nonneg (by linarith))
                    _ = Real.log p * (2 * ((1 / (p : ℝ)) ^ 2 - (1 / (p : ℝ)) ^ (K + 1))) := by
                        rw [← mul_sum, htel]
                    _ ≤ Real.log p * (2 * (1 / (p : ℝ)) ^ 2) := by
                        gcongr; linarith [pow_nonneg (show 0 ≤ 1 / (p : ℝ) by positivity) (K + 1)]
                    _ = 2 * Real.log p / (p : ℝ) ^ 2 := by ring
                have hlp : Real.log p ≤ 2 * √(p : ℝ) := by
                  have := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr (by linarith : (0 : ℝ) < p))
                  rw [Real.log_sqrt (by linarith)] at this; linarith
                refine hgeom.trans ?_
                have hsqp : √(p : ℝ) ^ 2 = p := Real.sq_sqrt (by linarith)
                rw [div_le_iff₀ (by positivity)]
                have h1 : 4 * (1 / ((p : ℝ) * √(p : ℝ))) * (p : ℝ) ^ 2 = 4 * √(p : ℝ) := by
                  have : √(p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
                  field_simp; nlinarith
                linarith
            _ ≤ ∑ p ∈ Icc 2 ⌊x⌋₊, 4 * (1 / ((p : ℝ) * √(p : ℝ))) := by
                refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => by positivity
                exact mem_Icc.mpr ⟨(mem_filter.mp hp).2.two_le, (mem_Ioc.mp (mem_filter.mp hp).1).2⟩
            _ = 4 * ∑ p ∈ Icc 2 ⌊x⌋₊, 1 / ((p : ℝ) * √(p : ℝ)) := (mul_sum ..).symm
            _ ≤ 8 := by linarith [sum_inv_mul_sqrt_le ⌊x⌋₊]
  have hm := abs_le.mp (sum_mangoldt_div_sub_log_le hx)
  rw [abs_le]; exact ⟨by linarith, by linarith⟩

/-- A sum over `primesIoc y z` is the difference of the prime prefix sums up to `z`
and `y`. -/
private lemma sum_primesIoc_eq (f : ℕ → ℝ) {y z : ℝ} (hyz : y ≤ z) :
    ∑ p ∈ primesIoc y z, f p =
      ∑ p ∈ Ioc 0 ⌊z⌋₊ with p.Prime, f p - ∑ p ∈ Ioc 0 ⌊y⌋₊ with p.Prime, f p := by
  have h := sum_Ioc_consecutive (fun p ↦ if p.Prime then f p else 0) (Nat.zero_le ⌊y⌋₊)
    (Nat.floor_le_floor hyz)
  simp only [primesIoc, sum_filter] at *
  linarith

/-- The primes up to `x` are those in `(0, x]`, since `1` is not prime. -/
private lemma primesIoc_one (x : ℝ) : primesIoc 1 x = (Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
  ext p
  simp only [primesIoc, Nat.floor_one, mem_filter, mem_Ioc]
  exact ⟨fun ⟨⟨_, h⟩, hp⟩ => ⟨⟨hp.pos, h⟩, hp⟩, fun ⟨⟨_, h⟩, hp⟩ => ⟨⟨hp.one_lt, h⟩, hp⟩⟩

/-- Mertens' first theorem on `(y, z]`. -/
theorem mertens_first : ∃ E : ℝ, 0 ≤ E ∧ ∀ y z : ℝ, 1 ≤ y → y ≤ z →
    |∑ p ∈ primesIoc y z, Real.log p / p - Real.log (z / y)| ≤ E := by
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨2 * (Real.log 4 + 12), by linarith, fun y z hy hyz => ?_⟩
  rw [sum_primesIoc_eq _ hyz, Real.log_div (by linarith) (by linarith)]
  have hy' := abs_le.mp (sum_log_prime_div_sub_log_le hy)
  have hz' := abs_le.mp (sum_log_prime_div_sub_log_le (hy.trans hyz))
  rw [abs_le]; constructor <;> linarith

private lemma abel_sum (S : ℕ → ℝ) {Y Z : ℕ} (hYZ : Y ≤ Z) :
    ∑ k ∈ Ico Y Z, (S (k + 1) - S k) / Real.log (k + 1 : ℕ) =
      S Z / Real.log Z - S Y / Real.log Y +
        ∑ k ∈ Ico Y Z, S k * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) := by
  induction Z, hYZ using Nat.le_induction with
  | base => simp
  | succ m hm ih => rw [sum_Ico_succ_top hm, sum_Ico_succ_top hm, ih]; ring

private lemma floor_sq_ge {t : ℝ} (ht : 2 ≤ t) : t ≤ (⌊t⌋₊ : ℝ) ^ 2 := by
  by_cases h3 : t < 3
  · have : (2 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast Nat.le_floor ht
    nlinarith
  · have := Nat.sub_one_lt_floor t; nlinarith

/-- Mertens' second theorem on `(y, z]`. -/
theorem mertens_second : ∃ E : ℝ, 0 ≤ E ∧ ∀ y z : ℝ, 2 ≤ y → y ≤ z →
    |∑ p ∈ primesIoc y z, (1 : ℝ) / p - Real.log (Real.log z / Real.log y)| ≤
      E / Real.log y := by
  set C₁ := Real.log 4 + 12
  have hC₁ : 0 ≤ C₁ := by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); linarith
  refine ⟨6 * C₁ + 6, by linarith, fun y z hy hyz => ?_⟩
  set Y := ⌊y⌋₊
  set Z := ⌊z⌋₊
  have hY2 : 2 ≤ Y := Nat.le_floor hy
  have hYZ : Y ≤ Z := Nat.floor_le_floor hyz
  have hlY : 0 < Real.log Y := Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hlZ : 0 < Real.log Z := Real.log_pos (by exact_mod_cast (show 1 < Z by omega))
  have hly : 0 < Real.log y := Real.log_pos (by linarith)
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  set S : ℕ → ℝ := fun k => ∑ p ∈ Ioc 0 k with p.Prime, Real.log p / p
  have hS : ∀ k : ℕ, 1 ≤ k → |S k - Real.log k| ≤ C₁ := fun k hk => by
    simpa [S, C₁] using sum_log_prime_div_sub_log_le (x := (k : ℝ)) (by exact_mod_cast hk)
  have hsum_eq : ∑ p ∈ primesIoc y z, (1 : ℝ) / p =
      ∑ k ∈ Ico Y Z, (S (k + 1) - S k) / Real.log (k + 1 : ℕ) := by
    have hstep : ∀ k ∈ Ico Y Z, (S (k + 1) - S k) / Real.log (k + 1 : ℕ) =
        if (k + 1).Prime then (1 : ℝ) / (k + 1 : ℕ) else 0 := by
      intro k _
      have hdiff : S (k + 1) - S k =
          if (k + 1).Prime then Real.log (k + 1 : ℕ) / (k + 1 : ℕ) else 0 := by
        simp only [S, sum_filter, sum_Ioc_succ_top (Nat.zero_le k), add_sub_cancel_left]
      rw [hdiff]
      split_ifs with hp
      · have hlk : Real.log (k + 1 : ℕ) ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
        field_simp
      · simp
    rw [sum_congr rfl hstep, sum_Ico_add' (fun m => if m.Prime then (1 : ℝ) / m else 0) Y Z 1]
    have hIoc : Ico (Y + 1) (Z + 1) = Ioc Y Z := by
      ext m; simp only [mem_Ico, mem_Ioc]; omega
    rw [hIoc, ← sum_filter]; rfl
  have htel1 : ∑ k ∈ Ico Y Z, (Real.log (Real.log (k + 1 : ℕ)) - Real.log (Real.log k)) =
      Real.log (Real.log Z) - Real.log (Real.log Y) :=
    sum_Ico_sub (fun k => Real.log (Real.log k)) hYZ
  have htel2 : ∑ k ∈ Ico Y Z, (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) =
      1 / Real.log Y - 1 / Real.log Z := by
    simpa only [neg_sub_neg] using sum_Ico_sub (fun k => -(1 / Real.log k)) hYZ
  have hdisc :
      |∑ p ∈ primesIoc y z, (1 : ℝ) / p - (Real.log (Real.log Z) - Real.log (Real.log Y))| ≤
        (3 * C₁ + 1) / Real.log Y := by
    rw [hsum_eq, abel_sum S hYZ, ← htel1]
    set r : ℕ → ℝ := fun k => S k - Real.log k
    have hbd : S Z / Real.log Z - S Y / Real.log Y = r Z / Real.log Z - r Y / Real.log Y := by
      have : ∀ k : ℕ, Real.log k ≠ 0 → S k / Real.log k = 1 + r k / Real.log k := fun k hk => by
        dsimp [r]; field_simp; ring
      rw [this Z hlZ.ne', this Y hlY.ne']; ring
    rw [hbd, add_sub_assoc, ← sum_sub_distrib]
    have hbnd_end : |r Z / Real.log Z - r Y / Real.log Y| ≤ 2 * C₁ / Real.log Y := by
      have h1 : |r Z / Real.log Z| ≤ C₁ / Real.log Y := by
        rw [abs_div, abs_of_pos hlZ]
        exact (div_le_div_of_nonneg_right (hS Z (by omega)) hlZ.le).trans
          (div_le_div_of_nonneg_left hC₁ hlY
            (Real.log_le_log (by positivity) (by exact_mod_cast hYZ)))
      have h2 : |r Y / Real.log Y| ≤ C₁ / Real.log Y := by
        rw [abs_div, abs_of_pos hlY]
        exact div_le_div_of_nonneg_right (hS Y (by omega)) hlY.le
      calc |r Z / Real.log Z - r Y / Real.log Y|
          ≤ |r Z / Real.log Z| + |r Y / Real.log Y| := abs_sub _ _
        _ ≤ C₁ / Real.log Y + C₁ / Real.log Y := add_le_add h1 h2
        _ = 2 * C₁ / Real.log Y := by ring
    have hbnd_sum : |∑ k ∈ Ico Y Z, (S k * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) -
        (Real.log (Real.log (k + 1 : ℕ)) - Real.log (Real.log k)))| ≤ (C₁ + 1) / Real.log Y := by
      refine (abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ Ico Y Z, |S k * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) -
            (Real.log (Real.log (k + 1 : ℕ)) - Real.log (Real.log k))|
          ≤ ∑ k ∈ Ico Y Z, (C₁ + 1) * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) := by
            refine sum_le_sum fun k hk => ?_
            have hk2 : 2 ≤ k := hY2.trans (mem_Ico.mp hk).1
            set A := Real.log k
            set B := Real.log (k + 1 : ℕ)
            have hA : 0 < A := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
            have hAB : A ≤ B := Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ k)
            have hB : 0 < B := hA.trans_le hAB
            have hinv : 0 ≤ 1 / A - 1 / B := sub_nonneg.mpr (one_div_le_one_div_of_le hA hAB)
            have hlow : (B - A) / B ≤ Real.log B - Real.log A := by
              have hexp := Real.one_sub_le_exp_neg ((B - A) / B)
              rw [show 1 - (B - A) / B = A / B by field_simp; ring] at hexp
              have hlg := Real.log_le_log (div_pos hA hB) hexp
              rw [Real.log_div hA.ne' hB.ne', Real.log_exp] at hlg; linarith
            have hhigh : Real.log B - Real.log A ≤ (B - A) / A := by
              have hexp := Real.add_one_le_exp ((B - A) / A)
              rw [show (B - A) / A + 1 = B / A by field_simp; ring] at hexp
              have hlg := Real.log_le_log (div_pos hB hA) hexp
              rw [Real.log_div hB.ne' hA.ne', Real.log_exp] at hlg; linarith
            have hBA1 : B - A ≤ 1 := by
              have hkpos : (0 : ℝ) < k := by positivity
              have hlg := Real.log_le_sub_one_of_pos
                (div_pos (show (0 : ℝ) < (k + 1 : ℕ) by positivity) hkpos)
              rw [Real.log_div (by positivity) hkpos.ne'] at hlg
              have h1k : ((k + 1 : ℕ) : ℝ) / k - 1 ≤ 1 := by
                rw [Nat.cast_add, Nat.cast_one, add_div, div_self hkpos.ne', add_sub_cancel_left]
                exact div_le_one_of_le₀ (by norm_cast; omega) hkpos.le
              linarith
            have hid : S k * (1 / A - 1 / B) - (Real.log B - Real.log A) =
                r k * (1 / A - 1 / B) - ((Real.log B - Real.log A) - (B - A) / B) := by
              have hAB' : A * (1 / A - 1 / B) = (B - A) / B := by field_simp
              have hSr : S k = A + r k := by dsimp [r]; ring
              rw [hSr, add_mul, hAB']; ring
            rw [hid]
            have hrk : |r k * (1 / A - 1 / B)| ≤ C₁ * (1 / A - 1 / B) := by
              rw [abs_mul, abs_of_nonneg hinv]
              exact mul_le_mul_of_nonneg_right (hS k (by omega)) hinv
            have hmid : (Real.log B - Real.log A) - (B - A) / B ≤ 1 / A - 1 / B := by
              have : (B - A) / A - (B - A) / B = (B - A) * (1 / A - 1 / B) := by ring
              nlinarith
            linarith [abs_sub (r k * (1 / A - 1 / B)) ((Real.log B - Real.log A) - (B - A) / B),
              abs_of_nonneg (sub_nonneg.mpr hlow)]
        _ = (C₁ + 1) * (1 / Real.log Y - 1 / Real.log Z) := by rw [← mul_sum, htel2]
        _ ≤ (C₁ + 1) / Real.log Y := by
            rw [mul_sub, mul_one_div]
            linarith [show 0 ≤ (C₁ + 1) * (1 / Real.log Z) by positivity]
    calc _ ≤ |r Z / Real.log Z - r Y / Real.log Y| +
          |∑ k ∈ Ico Y Z, (S k * (1 / Real.log k - 1 / Real.log (k + 1 : ℕ)) -
            (Real.log (Real.log (k + 1 : ℕ)) - Real.log (Real.log k)))| := abs_add_le _ _
      _ ≤ 2 * C₁ / Real.log Y + (C₁ + 1) / Real.log Y := add_le_add hbnd_end hbnd_sum
      _ = (3 * C₁ + 1) / Real.log Y := by ring
  have hfl_err : ∀ t : ℝ, 2 ≤ t →
      0 ≤ Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊) ∧
        Real.log (Real.log t) - Real.log (Real.log ⌊t⌋₊) ≤ 2 / Real.log t := by
    intro t ht
    have hT2 : 2 ≤ ⌊t⌋₊ := Nat.le_floor ht
    have hTpos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (show 0 < ⌊t⌋₊ by omega)
    have hlT : 0 < Real.log ⌊t⌋₊ := Real.log_pos (by exact_mod_cast (show 1 < ⌊t⌋₊ by omega))
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    have h1 : Real.log ⌊t⌋₊ ≤ Real.log t := Real.log_le_log hTpos (Nat.floor_le (by linarith))
    have h2 : Real.log t ≤ 2 * Real.log ⌊t⌋₊ := by
      have := Real.log_le_log (by linarith) (floor_sq_ge ht)
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    refine ⟨sub_nonneg.mpr (Real.log_le_log hlT h1), ?_⟩
    rw [← Real.log_div hlt.ne' hlT.ne']
    have h3 := Real.log_le_sub_one_of_pos (div_pos hlt hlT)
    have h4 : Real.log t / Real.log ⌊t⌋₊ - 1 = (Real.log t - Real.log ⌊t⌋₊) / Real.log ⌊t⌋₊ := by
      field_simp
    have h5 : Real.log t - Real.log ⌊t⌋₊ ≤ 1 := by
      rw [← Real.log_div (by linarith) hTpos.ne']
      have := Real.log_le_sub_one_of_pos (div_pos (by linarith : 0 < t) hTpos)
      have htT : t < ⌊t⌋₊ + 1 := Nat.lt_floor_add_one t
      have : t / ⌊t⌋₊ - 1 ≤ 1 := by
        rw [div_sub_one hTpos.ne', div_le_one hTpos]
        have : (1 : ℝ) ≤ ⌊t⌋₊ := by exact_mod_cast (show 1 ≤ ⌊t⌋₊ by omega)
        linarith
      linarith
    calc Real.log (Real.log t / Real.log ⌊t⌋₊)
        ≤ (Real.log t - Real.log ⌊t⌋₊) / Real.log ⌊t⌋₊ := h4 ▸ h3
      _ ≤ 1 / Real.log ⌊t⌋₊ := div_le_div_of_nonneg_right h5 hlT.le
      _ ≤ 2 / Real.log t := by rw [div_le_div_iff₀ hlT hlt]; linarith
  have hy_fl := hfl_err y hy
  have hz_fl := hfl_err z (hy.trans hyz)
  have hlY_inv : 1 / Real.log Y ≤ 2 / Real.log y := by
    have := Real.log_le_log (by linarith) (floor_sq_ge hy)
    rw [Real.log_pow, Nat.cast_ofNat] at this
    rw [div_le_div_iff₀ hlY hly]; linarith
  have hz_le_y : 2 / Real.log z ≤ 2 / Real.log y :=
    div_le_div_of_nonneg_left (by norm_num) hly (Real.log_le_log (by linarith) hyz)
  have hdisc' :
      |∑ p ∈ primesIoc y z, (1 : ℝ) / p - (Real.log (Real.log Z) - Real.log (Real.log Y))| ≤
        (6 * C₁ + 2) / Real.log y := by
    calc _ ≤ (3 * C₁ + 1) * (1 / Real.log Y) := by rw [mul_one_div]; exact hdisc
      _ ≤ (3 * C₁ + 1) * (2 / Real.log y) := mul_le_mul_of_nonneg_left hlY_inv (by linarith)
      _ = (6 * C₁ + 2) / Real.log y := by ring
  rw [Real.log_div hlz.ne' hly.ne']
  have hsplit : ∑ p ∈ primesIoc y z, (1 : ℝ) / p - (Real.log (Real.log z) - Real.log (Real.log y)) =
      (∑ p ∈ primesIoc y z, (1 : ℝ) / p - (Real.log (Real.log Z) - Real.log (Real.log Y))) -
        (Real.log (Real.log z) - Real.log (Real.log Z)) +
        (Real.log (Real.log y) - Real.log (Real.log Y)) := by ring
  rw [hsplit]
  have he1 : |Real.log (Real.log z) - Real.log (Real.log Z)| ≤ 2 / Real.log y := by
    rw [abs_of_nonneg hz_fl.1]; exact hz_fl.2.trans hz_le_y
  have he2 : |Real.log (Real.log y) - Real.log (Real.log Y)| ≤ 2 / Real.log y := by
    rw [abs_of_nonneg hy_fl.1]; exact hy_fl.2
  calc _ ≤ |∑ p ∈ primesIoc y z, (1 : ℝ) / p - (Real.log (Real.log Z) - Real.log (Real.log Y))| +
          |Real.log (Real.log z) - Real.log (Real.log Z)| +
          |Real.log (Real.log y) - Real.log (Real.log Y)| :=
        (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (6 * C₁ + 2) / Real.log y + 2 / Real.log y + 2 / Real.log y :=
        add_le_add (add_le_add hdisc' he1) he2
    _ = (6 * C₁ + 6) / Real.log y := by ring

/-- Mertens' second theorem with the constant absorbed: for `y ≥ 2`,
`|∑_{p ≤ y} 1 / p - log log y| ≤ E`. -/
lemma abs_sum_inv_primes_sub_le : ∃ E : ℝ, 0 ≤ E ∧ ∀ y : ℝ, 2 ≤ y →
    |∑ p ∈ primesIoc 1 y, (1 : ℝ) / p - Real.log (Real.log y)| ≤ E := by
  obtain ⟨E, hE, hM⟩ := mertens_second
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨E / Real.log 2 + |Real.log (Real.log 2)| + 1, by positivity, fun y hy => ?_⟩
  have h12 : primesIoc 1 y = insert 2 (primesIoc 2 y) := by
    ext p
    simp only [mem_insert, mem_primesIoc]
    constructor
    · rintro ⟨hp, _, hpy⟩
      rcases eq_or_lt_of_le hp.two_le with rfl | hp2
      · exact Or.inl rfl
      · exact Or.inr ⟨hp, by exact_mod_cast hp2, hpy⟩
    · rintro (rfl | ⟨hp, hp2, hpy⟩)
      · exact ⟨Nat.prime_two, by norm_num, hy⟩
      · exact ⟨hp, by linarith, hpy⟩
  have hnot : (2 : ℕ) ∉ primesIoc 2 y := by simp [mem_primesIoc]
  rw [h12, sum_insert hnot]
  have hm := hM 2 y le_rfl hy
  rw [Real.log_div (Real.log_pos (by linarith)).ne' hl2.ne'] at hm
  have hsub := abs_le.mp hm
  have := le_abs_self (Real.log (Real.log 2))
  have := neg_abs_le (Real.log (Real.log 2))
  have h12val : (1 : ℝ) / (2 : ℕ) = 1 / 2 := by norm_num
  rw [h12val, abs_le]; constructor <;> linarith

/-- Chebyshev's upper bound `π(x) ≪ x / log x`. -/
theorem card_primesIoc_le : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 2 ≤ x →
    ((primesIoc 1 x).card : ℝ) ≤ K * x / Real.log x := by
  have h4 : 0 ≤ Real.log 4 := log_nonneg (by norm_num)
  refine ⟨2 * Real.log 4 + 2, by linarith, fun x hx ↦ ?_⟩
  have hlx : 0 < Real.log x := log_pos (by linarith)
  have hcard : (primesIoc 1 x).card = Nat.primeCounting ⌊x⌋₊ := by
    rw [← Nat.primesLE_card_eq_primeCounting, primesIoc_one]
    congr 1; ext p
    simp only [mem_filter, mem_Ioc, Nat.primesLE, Nat.primesBelow, mem_range]
    exact ⟨fun ⟨⟨_, h⟩, hp⟩ => ⟨by omega, hp⟩, fun ⟨h, hp⟩ => ⟨⟨hp.pos, by omega⟩, hp⟩⟩
  have hpi := Chebyshev.pi_le_log4_mul_div (x := x) (by linarith)
  rw [log_sqrt (by linarith)] at hpi
  have hsx : 0 < √x := sqrt_pos.mpr (by linarith)
  have hlog : Real.log x ≤ 2 * √x := by
    have h := log_le_sub_one_of_pos hsx
    rw [log_sqrt (by linarith)] at h; linarith
  have hsqrt : √x ≤ 2 * x / Real.log x := by
    rw [le_div_iff₀ hlx]
    nlinarith [mul_self_sqrt (show 0 ≤ x by linarith)]
  rw [hcard]
  calc (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤ Real.log 4 * x / (Real.log x / 2) + √x := hpi
    _ ≤ Real.log 4 * x / (Real.log x / 2) + 2 * x / Real.log x := by gcongr
    _ = _ := by field_simp

/-- Chebyshev's upper bound `θ(x) = ∑_{p ≤ x} log p ≤ x log 4`. -/
theorem sum_log_primesIoc_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ p ∈ primesIoc 1 x, Real.log p ≤ Real.log 4 * x := by
  rw [primesIoc_one]
  exact Chebyshev.theta_le_log4_mul_x hx

/-- For `x ≥ 1` the dyad `(x, 2x]` contains a prime. -/
theorem dyadicPrimes_card_pos {x : ℝ} (hx : 1 ≤ x) : 0 < (dyadicPrimes x).card := by
  have hn : ⌊x⌋₊ ≠ 0 := (Nat.floor_pos.mpr hx).ne'
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ hn
  have h2 : 2 * ⌊x⌋₊ ≤ ⌊2 * x⌋₊ :=
    Nat.le_floor (by push_cast; linarith [Nat.floor_le (show 0 ≤ x by linarith)])
  exact card_pos.mpr ⟨p, mem_filter.mpr ⟨mem_Ioc.mpr ⟨hlt, hle.trans h2⟩, hp⟩⟩

end Erdos408
