module

public import Erdos408.Extraction.TypeII.Weights

/-!
# Regrouping the replacement sum

Generic identities and bounds for the double sum `∑_{m₀, n ≤ M} Ψ(m₀ n) α(m₀) β(n)` of one
telescoping step.

* Regrouping the companion factors by their product `n`.
* The clipped tail: if `|Ψ| ≤ S` vanishes above `M`, `|α| ≤ 1` and `0 ≤ β_t ≤ β h / B`, the
  tail is at most `S (M / B) ∑_{n ≤ M} β(n) h(n) / n`.
* The geometric grid `λ_a`: a sum over `[1, M]` of a function vanishing on `[1, λ_0]` and
  above `M` splits into the sums over the cells `(⌊λ_a⌋, ⌊λ_{a+1}⌋]`.
-/

@[expose] public section

namespace Erdos408.TypeII

open Finset

/-- Regrouping the companion factors of a telescoping step by their product. -/
theorem sum_tuple_eq_sum_fiber {M r : ℕ} (hr : 1 ≤ r) (Ψ : ℕ → ℝ)
    (hΨ : ∀ h, M < h → Ψ h = 0) (α : ℕ → ℝ) (v : Fin r → ℕ → ℝ) :
    ∑ m₀ ∈ Icc 1 M, ∑ m' ∈ Fintype.piFinset (fun _ : Fin r => Icc 1 M),
        Ψ (m₀ * ∏ k, m' k) * α m₀ * ∏ k, v k (m' k) =
      ∑ m₀ ∈ Icc 1 M, ∑ n ∈ Icc 1 M, Ψ (m₀ * n) * α m₀ * tupleWeight (Icc 1 M) v n := by
  refine sum_congr rfl fun m₀ hm₀ => ?_
  have hm₀1 : 1 ≤ m₀ := by grind
  have hT : ∀ m ∈ Fintype.piFinset (fun _ : Fin r => Icc 1 M), ∏ k, m k ∈ Icc 1 (M ^ r) := by
    intro m hm
    have hk := Fintype.mem_piFinset.1 hm
    refine mem_Icc.2 ⟨Finset.one_le_prod (by grind), ?_⟩
    calc ∏ k, m k ≤ ∏ _k : Fin r, M := prod_le_prod (by grind)
      _ = M ^ r := by simp
  rw [sum_piFinset_eq_sum_fiber (Icc 1 M) (fun n m' => Ψ (m₀ * n) * α m₀ * ∏ k, v k (m' k)) hT]
  simp only [← mul_sum]
  unfold tupleWeight
  symm
  refine sum_subset (fun n hn => ?_) fun n hn hnM => ?_
  · obtain ⟨h1, h2⟩ := mem_Icc.1 hn
    refine mem_Icc.2 ⟨h1, h2.trans ?_⟩
    calc M = M ^ 1 := by simp
      _ ≤ M ^ r := Nat.pow_le_pow_right (by omega) hr
  · have hn1 : 1 ≤ n := by grind
    have : M < n := by
      by_contra h
      exact by grind
    rw [hΨ _ (lt_of_lt_of_le this (Nat.le_mul_of_pos_left n hm₀1)), zero_mul, zero_mul]

/-- The clipped tail of a telescoping step. -/
theorem abs_sum_tail_le {M : ℕ} (Ψ α βt β h : ℕ → ℝ) {S B : ℝ} (hB : 0 < B)
    (hΨ0 : ∀ n, M < n → Ψ n = 0) (hΨ : ∀ n, |Ψ n| ≤ S) (hα : ∀ m, |α m| ≤ 1)
    (hβt : ∀ n, 0 ≤ βt n ∧ βt n ≤ β n * h n / B) :
    |∑ m₀ ∈ Icc 1 M, ∑ n ∈ Icc 1 M, Ψ (m₀ * n) * α m₀ * βt n| ≤
      S * (M / B) * ∑ n ∈ Icc 1 M, β n * h n / n := by
  have hS : 0 ≤ S := (abs_nonneg _).trans (hΨ 0)
  have hcount : ∀ n ∈ Icc 1 M, ∑ m₀ ∈ Icc 1 M, |Ψ (m₀ * n)| ≤ S * (M / n) := by
    intro n hn
    have hn1 : 1 ≤ n := by grind
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hsub : ∑ m₀ ∈ Icc 1 M, |Ψ (m₀ * n)| = ∑ m₀ ∈ Icc 1 (M / n), |Ψ (m₀ * n)| := by
      symm
      refine sum_subset (fun m hm => ?_) fun m hm hmn => ?_
      · obtain ⟨h1, h2⟩ := mem_Icc.1 hm
        exact mem_Icc.2 ⟨h1, h2.trans (Nat.div_le_self M n)⟩
      · have h1 := (mem_Icc.1 hm).1
        have : M / n < m := by
          by_contra h
          exact by grind
        have : M < m * n := by
          rw [Nat.div_lt_iff_lt_mul (by omega)] at this
          exact this
        simp_all
    rw [hsub]
    calc ∑ m₀ ∈ Icc 1 (M / n), |Ψ (m₀ * n)| ≤ ∑ _m₀ ∈ Icc 1 (M / n), S :=
          sum_le_sum (by grind)
      _ = S * (M / n : ℕ) := by rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; grind
      _ ≤ S * (M / n) := mul_le_mul_of_nonneg_left Nat.cast_div_le hS
  calc |∑ m₀ ∈ Icc 1 M, ∑ n ∈ Icc 1 M, Ψ (m₀ * n) * α m₀ * βt n|
      ≤ ∑ m₀ ∈ Icc 1 M, ∑ n ∈ Icc 1 M, |Ψ (m₀ * n)| * βt n := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m₀ _ => ?_)
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
        rw [abs_mul, abs_mul, abs_of_nonneg (hβt n).1, mul_comm |Ψ _| |α m₀|, mul_assoc]
        exact mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (by grind)) (by grind)
    _ = ∑ n ∈ Icc 1 M, βt n * ∑ m₀ ∈ Icc 1 M, |Ψ (m₀ * n)| := by
        rw [sum_comm]
        exact sum_congr rfl fun n _ => by rw [mul_sum]; grind
    _ ≤ ∑ n ∈ Icc 1 M, β n * h n / B * (S * (M / n)) := by
        refine sum_le_sum fun n hn => ?_
        exact mul_le_mul (by grind) (by grind) (by positivity)
          (by grind)
    _ = S * (M / B) * ∑ n ∈ Icc 1 M, β n * h n / n := by
        rw [mul_sum]
        grind

/-- Consecutive cells `(⌊λ_a⌋, ⌊λ_{a+1}⌋]` add up to `(⌊λ_0⌋, ⌊λ_A⌋]`. -/
theorem sum_cells_eq {R : Type*} [AddCommMonoid R] (f : ℕ → R) (lam : ℕ → ℝ)
    (hmono : ∀ a, lam a ≤ lam (a + 1)) (A : ℕ) :
    ∑ a ∈ range A, ∑ m ∈ Ioc ⌊lam a⌋₊ ⌊lam (a + 1)⌋₊, f m =
      ∑ m ∈ Ioc ⌊lam 0⌋₊ ⌊lam A⌋₊, f m := by
  induction A with
  | zero => simp
  | succ A ih =>
    rw [sum_range_succ, ih]
    have h0A : ⌊lam 0⌋₊ ≤ ⌊lam A⌋₊ :=
      Nat.floor_le_floor (monotone_nat_of_le_succ hmono (Nat.zero_le A))
    exact sum_Ioc_consecutive f h0A (Nat.floor_le_floor (hmono A))

/-- A sum over `[1, M]` of a function vanishing on `[1, λ_0]` and above `M` is the sum over
the cells of a grid reaching `M`. -/
theorem sum_Icc_eq_sum_cells {R : Type*} [AddCommMonoid R] (f : ℕ → R) (lam : ℕ → ℝ)
    (hmono : ∀ a, lam a ≤ lam (a + 1)) (h0 : 0 ≤ lam 0) {M A : ℕ} (hA : (M : ℝ) ≤ lam A)
    (hlow : ∀ m : ℕ, 1 ≤ m → (m : ℝ) ≤ lam 0 → f m = 0) (hhigh : ∀ m, M < m → f m = 0) :
    ∑ m ∈ Icc 1 M, f m = ∑ a ∈ range A, ∑ m ∈ Ioc ⌊lam a⌋₊ ⌊lam (a + 1)⌋₊, f m := by
  rw [sum_cells_eq f lam hmono A]
  have hMA := Nat.le_floor hA
  have h0A : ⌊lam 0⌋₊ ≤ ⌊lam A⌋₊ :=
    Nat.floor_le_floor (monotone_nat_of_le_succ hmono (Nat.zero_le A))
  have e1 : ∑ m ∈ Icc 1 M, f m = ∑ m ∈ Ioc 0 ⌊lam A⌋₊, f m := by
    refine sum_subset (fun m hm => ?_) fun m hm hmM => ?_
    · grind
    · grind
  have e2 : ∑ m ∈ Ioc ⌊lam 0⌋₊ ⌊lam A⌋₊, f m = ∑ m ∈ Ioc 0 ⌊lam A⌋₊, f m := by
    refine sum_subset (fun m hm => ?_) fun m hm hm0 => ?_
    · grind
    · obtain ⟨h1, h2⟩ := mem_Ioc.1 hm
      have : m ≤ ⌊lam 0⌋₊ := by
        by_contra h
        exact hm0 (mem_Ioc.2 ⟨by omega, h2⟩)
      exact hlow m h1 ((Nat.le_floor_iff h0).1 this)
  simp_all

end Erdos408.TypeII
