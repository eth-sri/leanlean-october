/-
Adapted from PrimeNumberTheoremAnd/IEANTN/Mertens.lean (Apache-2.0).
-/
module

public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section
namespace CCDN.Mertens

open Real Finset
open ArithmeticFunction hiding log

private lemma sum_log_nat : ∀ N : ℕ, (N : ℝ) * log N - N ≤ ∑ n ∈ Ioc 0 N, log n
  | 0 => by simp
  | N + 1 => by
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    · have h0 : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
      have h := mul_le_mul_of_nonneg_left
        (log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (N + 1 : ℕ)) h0)) h0.le
      rw [log_div (by positivity) h0.ne'] at h
      rw [sum_Ioc_succ_top (Nat.zero_le N)]
      have ih := sum_log_nat N
      push_cast at h ⊢; field_simp at h; linarith

private lemma prime_tail_aux : ∀ N : ℕ,
    (∑ p ∈ Ioc 0 (N + 1) with p.Prime, log p / ((p : ℝ) * (p - 1))) + 6 / sqrt (N + 1 : ℕ) ≤ 6
  | 0 => by rw [sum_filter]; simp
  | N + 1 => by
    have ih := prime_tail_aux N
    rw [sum_filter, sum_Ioc_succ_top (Nat.zero_le _), ← sum_filter]
    split_ifs with hp
    · set a := sqrt (N + 1 : ℕ)
      set b := sqrt (N + 2 : ℕ)
      have ha2 : a ^ 2 = (N + 1 : ℕ) := sq_sqrt (by positivity)
      have hb2 : b ^ 2 = (N + 2 : ℕ) := sq_sqrt (by positivity)
      have ha0 : 0 < a := sqrt_pos.mpr (by positivity)
      have hb0 : 0 < b := sqrt_pos.mpr (by positivity)
      have hlog : log (N + 2 : ℕ) ≤ 2 * b := by
        have hlb : log (N + 2 : ℕ) = 2 * log b := by rw [← hb2, log_pow]; ring
        linarith [log_le_sub_one_of_pos hb0]
      have h1 : (3 * a ^ 2 + 1) ^ 2 ≤ (3 * a * b) ^ 2 := by push_cast at ha2 hb2; nlinarith
      have hsq : 1 ≤ 3 * a * (b - a) := by linarith [(sq_le_sq₀ (by positivity) (by positivity)).mp h1]
      have hstep : log (N + 2 : ℕ) / ((N + 2 : ℕ) * ((N + 2 : ℕ) - 1 : ℝ)) ≤ 6 / a - 6 / b := by
        have hsub : ((N + 2 : ℕ) - 1 : ℝ) = a ^ 2 := by push_cast at ha2 ⊢; linarith
        rw [hsub, div_le_iff₀ (by positivity)]
        have : (6 / a - 6 / b) * ((N + 2 : ℕ) * a ^ 2) = 6 * a * b * (b - a) := by
          rw [← hb2]; field_simp
        rw [this]; nlinarith
      linarith
    · have : 6 / sqrt (N + 2 : ℕ) ≤ 6 / sqrt (N + 1 : ℕ) := by gcongr; omega
      linarith

theorem prime_sum_bounded_error {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p / p - log x| ≤ log 4 + 12 := by
  have hN1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast (by simpa : 1 ≤ ⌊x⌋₊)
  have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxN : x ≤ ⌊x⌋₊ + 1 := (Nat.lt_floor_add_one x).le
  have hmang : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    have h : ∀ n : ℕ, log n = (Λ * zeta) n := fun n => by rw [vonMangoldt_mul_zeta]; rfl
    simp_rw [h, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]
  have hge_log : x * log x - 2 * x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, log n := by
    have h1 : (x - ⌊x⌋₊) * log x ≤ x - 1 := by
      nlinarith [log_nonneg hx, log_le_sub_one_of_pos (by linarith : 0 < x)]
    have h2 := mul_le_mul_of_nonneg_left
      (log_le_sub_one_of_pos (div_pos (by linarith : 0 < x) (by linarith : 0 < (⌊x⌋₊ : ℝ))))
      (by linarith : (0 : ℝ) ≤ ⌊x⌋₊)
    rw [log_div (by linarith) (by linarith)] at h2
    field_simp at h2; linarith [sum_log_nat ⌊x⌋₊]
  have hle_log : ∑ n ∈ Ioc 0 ⌊x⌋₊, log n ≤ x * log x :=
    (sum_le_sum fun n hn => log_le_log (by exact_mod_cast (mem_Ioc.mp hn).1)
      ((Nat.le_floor_iff (by linarith)).mp (mem_Ioc.mp hn).2)).trans <| by
      simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hNx (log_nonneg hx)
  have hmul : x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring
  have hΛ_ge : x * (log x - 2) ≤ x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d := by
    rw [hmul, mul_sub]
    refine (by linarith [hmang, hge_log] : x * log x - x * 2 ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊).trans ?_
    gcongr with d; exact Nat.floor_le (div_nonneg (by linarith) (Nat.cast_nonneg d))
  have hΛ_le : x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) := by
    rw [hmul]
    refine (sum_le_sum fun d _ => mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one _).le
      vonMangoldt_nonneg).trans ?_
    simp_rw [mul_add, mul_one]; rw [sum_add_distrib, ← hmang]
    exact (add_le_add hle_log (Chebyshev.psi_le_const_mul_self (by linarith))).trans_eq (by ring)
  have hp_le : ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p / p ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d := by
    rw [sum_filter]; refine sum_le_sum fun d _ => ?_
    split_ifs with hd; · simp [vonMangoldt_apply_prime hd]
    exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg d)
  have hΛ_le_p : ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ (∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p / p) + 6 := by
    set M := max 1 ⌊log x / log 2⌋₊
    simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter,
      Chebyshev.sum_PrimePow_eq_sum_sum' _ (by linarith : 0 ≤ x) (le_max_right 1 _)]
    calc _ = ∑ k ∈ Icc 1 M, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with p.Prime, log p / (p ^ k : ℕ) :=
          sum_congr rfl fun k hk => sum_congr rfl fun p hp => by
            rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
      _ ≤ ∑ k ∈ Icc 1 M, ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p / (p ^ k : ℕ) := by
          gcongr with k hk
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (mem_Icc.mp hk).1
          exact rpow_le_self_of_one_le hx ((div_le_one (show (0 : ℝ) < k by linarith)).mpr hk1)
      _ = _ + ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, log p * ∑ k ∈ Ico 2 (M + 1), ((p : ℝ)⁻¹) ^ k := by
          rw [← add_sum_Ioc_eq_sum_Icc (le_max_left 1 _)]
          simp only [pow_one, Nat.cast_pow]; congr 1
          rw [sum_comm, show Ioc 1 M = Ico 2 (M + 1) from rfl]
          refine sum_congr rfl fun p _ => ?_
          rw [mul_sum]; exact sum_congr rfl fun k _ => by rw [inv_pow, div_eq_mul_inv]
      _ ≤ _ := by
          gcongr
          refine (sum_le_sum (g := fun p : ℕ => log p / ((p : ℝ) * (p - 1))) fun p hp => ?_).trans
            ((sum_le_sum_of_subset_of_nonneg (f := fun p : ℕ => log p / ((p : ℝ) * (p - 1)))
              (filter_subset_filter _ (Ioc_subset_Ioc_right (Nat.le_succ ⌊x⌋₊))) fun p hp _ => by
                have : (1 : ℝ) ≤ p := by exact_mod_cast (mem_filter.mp hp).2.one_le
                exact div_nonneg (log_natCast_nonneg p) (by nlinarith)).trans
              (by linarith [prime_tail_aux ⌊x⌋₊, show 0 ≤ 6 / sqrt (⌊x⌋₊ + 1 : ℕ) by positivity]))
          have hp2 := (mem_filter.mp hp).2
          have hgeom := geom_sum_Ico_le_of_lt_one (x := (p : ℝ)⁻¹) (m := 2) (n := M + 1)
            (by positivity) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp2.one_lt))
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hp2.pos
          exact (mul_le_mul_of_nonneg_left hgeom (log_natCast_nonneg p)).trans_eq (by field_simp)
  have := le_of_mul_le_mul_left hΛ_ge (by linarith : 0 < x)
  have := le_of_mul_le_mul_left hΛ_le (by linarith : 0 < x)
  have := log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end CCDN.Mertens
