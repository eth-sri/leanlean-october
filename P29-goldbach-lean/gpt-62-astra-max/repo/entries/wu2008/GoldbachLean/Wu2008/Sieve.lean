module

public import Mathlib

/-!
# Sieve counts S(A_e; P(D), y)

Definitions shared by the Wu 2008 Lemma 2.2 development: `Sifted`, `S`, `PS`, as in
LeanLab/ChenDoubleSieve/Lemma41.lean of the Lean Lab, unit U-5400. AI wrote the Lean code.
-/

open Finset

@[expose] public noncomputable section
open scoped Classical

namespace GoldbachLean.Wu2008.WuSieve

variable (A : Finset ℕ) (e D N : ℕ) (y : ℝ) (a : ℕ)

/-- `a` survives sifting by `P(D) = {q prime : q ∤ D}` up to `y`. -/
def Sifted :=
  ∀ q : ℕ, q.Prime → q < y → ¬ q ∣ D → ¬ q ∣ a

/-- `S(A_e; P(D), y)`. -/
def S :=
  #{a ∈ A | e ∣ a ∧ Sifted D y a}

/-- The primes `p` with `w ≤ p < z` and `(p, N) = 1`. -/
def PS (w z : ℝ) : Finset ℕ :=
  {p ∈ range ⌈z⌉₊ | p.Prime ∧ w ≤ p ∧ p < z ∧ p.Coprime N}

variable {A N D y a}

/-- Sifting only tests prime factors of the sequence member. -/
lemma factors (h : a ≠ 0) :
    Sifted D y a ↔ ∀ p ∈ a.primeFactors, ⌈y⌉₊ ≤ p ∨ p ∣ D := by
  simp [Sifted, h]; grind

lemma sifted_iff (h : a ≠ 0) (hc : a.Coprime D) :
    Sifted D y a ↔ ∀ p ∈ a.primeFactors, ⌈y⌉₊ ≤ p := by
  grind [factors h, Nat.eq_one_of_dvd_coprimes, Nat.Prime.ne_one]

/-- Sequence members are positive, below `N`, and coprime to `N`. -/
scoped notation:50 a " eligibleFor " N => 0 < a ∧ a < N ∧ Nat.Coprime a N

/-- The number of nonsquarefree sifted members, bounded by summing the multiples of
squares in the inverse-square tail above the sieve level `y`. After dropping the primality
condition, `sum_Ioc_inv_sq_le_sub` bounds that tail by `1 / (y - 1)`. -/
lemma squareful_le (hu : 1 < y) (hAN : ∀ a ∈ A, a eligibleFor N) :
    (#{a ∈ A | Sifted N y a ∧ ¬Squarefree a} : ℝ) ≤ N / (y - 1) := by
  have h := sub_pos.mpr hu
  have hm := Nat.ceil_pos.mpr h
  have bound := (sum_Ioc_inv_sq_le_sub (α := ℝ) hm.ne' (le_max_left _ N)).trans
    ((sub_le_self _ (by positivity)).trans (inv_anti₀ h (Nat.le_ceil _)))
  -- It suffices to count multiples of the squares in this (possibly enlarged) interval.
  grw [div_eq_mul_inv, ← bound, mul_sum]
  simp_rw [pow_two, ← Nat.cast_mul, ← div_eq_mul_inv]
  grw [← Nat.cast_div_le]
  norm_cast
  simp_rw [← Nat.Ioc_filter_dvd_card_eq_div]
  apply (card_le_card ?_).trans card_biUnion_le
  intro a ha
  simp [Nat.squarefree_iff_prime_squarefree] at ha
  obtain ⟨ha, hs, q, hq, hd⟩ := ha
  obtain ⟨h0, haN, hc⟩ := hAN a ha
  have hq' := hq.mem_primeFactors (dvd_of_mul_right_dvd hd) h0.ne'
  apply mem_biUnion.mpr ⟨q, ?_, ?_⟩ <;>
    grind [sifted_iff h0.ne' hc, Nat.ceil_sub_one, Nat.le_of_mem_primeFactors hq']

end GoldbachLean.Wu2008.WuSieve
