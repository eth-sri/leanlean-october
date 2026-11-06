module

public import Chazelle.Chain.Sides

/-!
# Mirror symmetry (F-D7), part 2: the reflection of walk keys

A walk traversed backwards (the mirror image of a walk, reversed so that the domain stays on its
left) sees the key `x ∈ [0, n)` of a position at the key `rk n c x = (c - x) mod n`, for a fixed
shift `c < n`.  This is an involution of `[0, n)` that reverses the cyclic order: the open cyclic
interval `(a, b)` maps to `(rk b, rk a)` (`sideInArc_rk`).
-/

namespace Chazelle.Core

namespace Mir

@[expose] public section

open Chazelle.Chain (sideInArc)

/-- **The reflected key** `(c - x) mod n` on `[0, n)`. -/
noncomputable def rk (n c : ℕ) (x : ℝ) : ℝ := if x ≤ c then c - x else c - x + n

macro "mcyc" : tactic => `(tactic| (
  (try simp only [not_and_or, not_or, not_lt, not_le] at *) <;>
  (casesm* _ ∧ _, _ ∨ _) <;>
  first
  | linarith
  | (constructor! <;> linarith)
  | (left; constructor <;> linarith) | (right; constructor <;> linarith)
  | (left; linarith) | (right; linarith)))

variable {n c : ℕ}

theorem rk_bounds (hc : c < n) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x < n) : 0 ≤ rk n c x ∧ rk n c x < n := by
  have hc' : (c : ℝ) < n := by exact_mod_cast hc
  unfold rk; split_ifs with h <;> constructor <;> linarith

theorem rk_rk (hc : c < n) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x < n) : rk n c (rk n c x) = x := by
  have hc' : (c : ℝ) < n := by exact_mod_cast hc
  unfold rk
  split_ifs with h1 h2 h2 <;> linarith

/-- The reflected key of a walk vertex. -/
theorem rk_nat (hc : c < n) {p : ℕ} (hp : p < n) : rk n c p = ((c + n - p) % n : ℕ) := by
  unfold rk
  split_ifs with h
  · have h' : p ≤ c := by exact_mod_cast h
    rw [show (c + n - p) % n = c - p by
      rw [show c + n - p = (c - p) + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]]
    push_cast [h']; ring
  · have h' : c < p := by
      by_contra hh; push Not at hh; exact h (by exact_mod_cast hh)
    rw [Nat.mod_eq_of_lt (by omega : c + n - p < n)]
    push_cast [show p ≤ c + n by omega]; ring

/-- The reflected key of an interior point of a walk edge. -/
theorem rk_edge (hc : c < n) {p : ℕ} (hp : p < n) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    rk n c (p + t) = ((c + 2 * n - 1 - p) % n : ℕ) + (1 - t) := by
  unfold rk
  split_ifs with h
  · have h' : p < c := by
      by_contra hh; push Not at hh
      have : (c : ℝ) ≤ p := by exact_mod_cast hh
      linarith
    rw [show (c + 2 * n - 1 - p) % n = c - 1 - p by
      rw [show c + 2 * n - 1 - p = (c - 1 - p) + n * 2 by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]]
    have e : ((c - 1 - p : ℕ) : ℝ) = (c : ℝ) - 1 - p := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e]; ring
  · have h' : c ≤ p := by
      by_contra hh; push Not at hh
      have : (p : ℝ) + 1 ≤ c := by exact_mod_cast hh
      linarith
    rw [show (c + 2 * n - 1 - p) % n = c + n - 1 - p by
      rw [show c + 2 * n - 1 - p = (c + n - 1 - p) + n * 1 by omega, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by omega)]]
    have e : ((c + n - 1 - p : ℕ) : ℝ) = (c : ℝ) + n - 1 - p := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring
    rw [e]; ring

/-- **The reflection reverses the cyclic order.** -/
theorem sideInArc_rk (hc : c < n) {a b x : ℝ} (ha0 : 0 ≤ a) (han : a < n) (hb0 : 0 ≤ b)
    (hbn : b < n) (hx0 : 0 ≤ x) (hxn : x < n) :
    sideInArc a b x ↔ sideInArc (rk n c b) (rk n c a) (rk n c x) := by
  have hc' : (c : ℝ) < n := by exact_mod_cast hc
  unfold rk sideInArc
  split_ifs <;> constructor <;> intro h <;> mcyc

end

end Mir

end Chazelle.Core
