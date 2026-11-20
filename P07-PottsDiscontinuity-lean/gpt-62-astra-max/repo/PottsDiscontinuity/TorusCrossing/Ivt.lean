module

public import Mathlib.Logic.Relation
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic

/-!
# A discrete intermediate value property for paths

If a path moves the integer level `r` by at most one at each step, then a path from level `≤ c` to
level `≥ c + k` contains a sub-path from level `c` to level `c + k` staying in the levels
`[c, c + k]`.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing

open Relation

variable {α : Type*} (R : α → α → Prop) (r : α → ℤ)

variable (hstep : ∀ p q, R p q → r q ≤ r p + 1 ∧ r p ≤ r q + 1) (c : ℤ) (k : ℕ) {a b : α}
    (hab : ReflTransGen R a b) (ha : r a ≤ c)
include hstep

include hab ha in
theorem ivt_lower (hb : c ≤ r b) :
    ∃ x, r x = c ∧ ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ c ≤ r q) x b := by
  have hge : ∀ x b, r x = c →
      ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ c ≤ r q) x b → c ≤ r b := by
    grind
  have key : ∀ b, ReflTransGen R a b →
      r b < c ∨ ∃ x, r x = c ∧ ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ c ≤ r q) x b := by
    intro b hb
    induction hb with
    | refl =>
      grind
    | @tail b b' _ hbb' ih =>
      grind
  grind

theorem ivt_upper {x b : α}
    (hx : r x = c) (hxb : ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ c ≤ r q) x b)
    (hb : c + k ≤ r b) :
    ∃ y, r y = c + k ∧
      ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ r p ≤ c + k ∧ c ≤ r q ∧ r q ≤ c + k) x y := by
  have key : ∀ b, ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ c ≤ r q) x b →
      (r b ≤ c + k ∧ ReflTransGen
        (fun p q => R p q ∧ c ≤ r p ∧ r p ≤ c + k ∧ c ≤ r q ∧ r q ≤ c + k) x b) ∨
      ∃ y, r y = c + k ∧
        ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ r p ≤ c + k ∧ c ≤ r q ∧ r q ≤ c + k) x y := by
    intro b hb
    induction hb with
    | refl => grind
    | @tail b b' _ hbb' ih =>
      grind
  rcases key b hxb with ⟨hle, hpath⟩ | h
  · grind
  · exact h

include hab ha in
theorem ivt_path (hb : c + k ≤ r b) :
    ∃ x y, r x = c ∧ r y = c + k ∧
      ReflTransGen (fun p q => R p q ∧ c ≤ r p ∧ r p ≤ c + k ∧ c ≤ r q ∧ r q ≤ c + k) x y := by
  obtain ⟨x, hx, hxb⟩ := ivt_lower R r hstep c hab ha (by omega)
  obtain ⟨y, hy, hxy⟩ := ivt_upper R r hstep c k hx hxb hb
  grind

end PottsDiscontinuity.TorusCrossing
