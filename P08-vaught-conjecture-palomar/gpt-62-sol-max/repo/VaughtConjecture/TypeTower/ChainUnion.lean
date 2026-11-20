/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.TypeTower.RealizationExtension

@[expose] public section

namespace VaughtConjecture.TypeTower.Realization

universe u v w

variable {Λ : Type v} [Preorder Λ] {T : TypeTower.{u} Λ} {α : Λ} {M : Type w}

open Classical in
/-- The union chooses any stage at which a tuple is defined. -/
noncomputable def chainUnion (A : ℕ → T.Realization α M) : T.Realization α M where
  eval t := if h : ∃ k, ((A k).eval t).isSome then (A h.choose).eval t else none

variable {A : ℕ → T.Realization α M}

theorem chainUnion_eval_some_exists {n : ℕ} {t : Fin n ↪ M} {p : T.Ty α n}
    (hp : (chainUnion A).eval t = some p) : ∃ k, (A k).eval t = some p := by
  by_cases h : ∃ k, ((A k).eval t).isSome
  · grind +locals
  grind +locals

theorem extends_of_le (hchain : ∀ k, (A k).Extends (A (k + 1))) {j k : ℕ} (hjk : j ≤ k) :
    (A j).Extends (A k) := by
  induction hjk with
  | refl => exact Extends.refl _
  | step _ ih => tauto

theorem extends_chainUnion (hchain : ∀ k, (A k).Extends (A (k + 1))) (k : ℕ) :
    (A k).Extends (chainUnion A) := by
  intro n t p hp
  have h : ∃ j, ((A j).eval t).isSome := by grind
  have he : (chainUnion A).eval t = (A h.choose).eval t := dite_eq_left h
  rcases Nat.le_total k h.choose with hk | hk
  · exact he.trans (extends_of_le hchain hk t p hp)
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp h.choose_spec
    rw [he, hq]
    exact (extends_of_le hchain hk t q hq).symm.trans hp

theorem chainUnion_consistent (hchain : ∀ k, (A k).Extends (A (k + 1)))
    (hcons : ∀ k, (A k).IsExactParentConsistent) :
    (chainUnion A).IsExactParentConsistent := by
  intro m n t p f hp
  obtain ⟨j, hj⟩ := chainUnion_eval_some_exists hp
  cases h : T.pull f p with
  | some q => exact extends_chainUnion hchain j _ q ((hcons j t p f hj).trans h)
  | none =>
    cases he : (chainUnion A).eval (f.trans t) with
    | none => rfl
    | some q =>
      obtain ⟨i, hi⟩ := chainUnion_eval_some_exists he
      have hp' := extends_of_le hchain (le_max_right i j) t p hj
      have hq' := extends_of_le hchain (le_max_left i j) _ q hi
      have hc := (hcons (max i j) t p f hp').symm.trans hq'
      lia

end VaughtConjecture.TypeTower.Realization
