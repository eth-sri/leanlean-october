module

public import Mathlib

/-! # The combinatorial accounting in Wu's lemma

The positive pair counts together count `edges`: increasing pairs with first prime below `z`
and second below `m`. Split off the two least factors `p, q`. Every edge in the remaining tail
is paid for by a quadruple with prefix `(p, q)`; the edges incident to `p, q` can be counted by
single-prime counts. This avoids a change of variables to real exponents.
-/

@[expose] public section
open Finset
namespace GoldbachLean.Wu2008.Counting

variable (s : Finset ℕ)

def below w := #{p ∈ s | p < w}

def edges z m := (s ×ˢ s).filter fun ⟨p, q⟩ => p < q ∧ p < z ∧ q < m

variable {s}

private lemma edges_insert {p} (hp : ∀ x ∈ s, p < x) (z m) :
    #(edges (insert p s) z m) = (if p < z then below s m else 0) + #(edges s z m) := by
  by_cases p < z <;>
    simp +contextual (disch := grind) [*, edges, below, card_filter, -sum_boole, sum_product, sum_insert,
      fun x hx => (hp x hx).not_gt]

/-- Charge tail edges to Υ₁₀ and Υ₁₁. The exceptional pairs counted by Υ₇, Υ₈, and Υ₉
cover the remaining deficit when the first two factors lie in the indicated ranges. The resulting
weight is at most four for at most two factors, and nonpositive otherwise. -/
lemma accounting {z m e n₇ n₈ n₉ n₁₀ n₁₁ : ℕ}
    (hzm : z ≤ m) (hme : m ≤ e)
    (charge : ∀ p q t, s = insert p (insert q t) → p < q → (∀ x ∈ t, q < x) → t.Nonempty →
      p < e ∧ #(edges t z m) ≤ n₁₀ + n₁₁ ∧ (m ≤ p → 0 < n₇) ∧ (e ≤ q → 0 < n₈) ∧
        (z ≤ p → p < m → m ≤ q → below t e = 0 → 0 < n₉)) :
    3 + (if ∀ x ∈ s, z ≤ x then (1 : ℤ) else 0) + #(edges s z m) - below s e - below s m
      - 2 * n₇ - n₈ - n₉ - n₁₀ - n₁₁ ≤ if #s ≤ 2 then 4 else 0 := by
  cases s using induction_on_min
  · simp [edges, below]; omega
  rename_i p u hp ih
  cases u using induction_on_min
  · simp [edges, below, filter_singleton]; grind
  rename_i q t hq ih
  simp (disch := grind) only [edges_insert, below, filter_insert, apply_ite card, card_insert_of_notMem,
    forall_mem_insert]
  -- Only the three ranges of the two least factors and the presence of a tail
  -- factor below e now matter. The remaining budget is linear arithmetic.
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp [edges]; grind
  specialize charge _ _ _ rfl (by grind) hq ht
  have hme' : below t m ≤ below t e := by unfold below; gcongr
  grind [below]

end GoldbachLean.Wu2008.Counting
