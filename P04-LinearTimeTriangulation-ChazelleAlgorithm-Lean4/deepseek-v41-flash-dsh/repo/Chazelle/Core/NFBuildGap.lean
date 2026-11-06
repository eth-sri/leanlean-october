module

public import Chazelle.Golf

public import Chazelle.Core.NFBuildSort

/-!
# WP-C (BuildNF): gaps of a sorted event list

Abstract list facts used to read the stack pass over the sorted events as a statement about keys:

* `take_cntBelow`: in an event list sorted by `EvLe`, the events with key below `x` (no event
  key equal to `x`) form a prefix, of length `cntBelow S x`;
* `count_two`: the number of occurrences of a chord index in the chord word of a duplicate-free
  sublist, when the chord has exactly two events;
* `mem_split_of_ne`, `evLe_of_mem_left`, `evLe_of_mem_right`: an event list split at an event.
-/

namespace Chazelle.Core.BuildSort

@[expose] public section

open List

/-- The number of events with key below `x`. -/
noncomputable def cntBelow (S : List Ev) (x : ℝ) : ℕ := S.countP (fun e => decide (e.2.1 < x))

/-- The order of events refines the order of keys. -/
theorem key_le_of_evLe {n : ℝ} {e f : Ev} (h : EvLe n e f) : e.2.1 ≤ f.2.1 := by
  rcases h with h | h
  · exact h.le
  · exact h.1.le

/-- **The events below a key form a prefix** of a sorted event list. -/
theorem take_cntBelow {n : ℝ} {S : List Ev} (hs : S.Pairwise (EvLe n)) {x : ℝ}
    (hx : ∀ e ∈ S, e.2.1 ≠ x) : S.take (cntBelow S x) = S.filter (fun e => decide (e.2.1 < x)) := by
  induction S with
  | nil => rfl
  | cons e S ih =>
    rw [pairwise_cons] at hs
    have ih' := ih hs.2 (fun f hf => hx f (mem_cons_of_mem e hf))
    unfold cntBelow at ih' ⊢
    Ξ countP_cons, filter_cons
    by_cases he : e.2.1 < x
    · ϴ he, decide_true, ite_true
      Ξ take_succ_cons, ih'
    · have hgt : x < e.2.1 := lt_of_le_of_ne (not_lt.1 he) (Ne.symm (hx e mem_cons_self))
      have hall : ∀ f ∈ S, ¬ f.2.1 < x := fun f hf h =>
        absurd (h.trans_le' (key_le_of_evLe (hs.1 f hf))) (⟡)
      have h0 : S.countP (fun e => decide (e.2.1 < x)) = 0 := by
        rw [countP_eq_zero]; intro f hf; simpa using hall f hf
      have h1 : S.filter (fun e => decide (e.2.1 < x)) = [] := by
        rw [filter_eq_nil_iff]; intro f hf; simpa using hall f hf
      ϴ he, decide_false, ite_false, h0, h1, add_zero, Bool.false_eq_true
      rfl

/-- The chord word of the events below a key. -/
theorem take_map_cntBelow {n : ℝ} {S : List Ev} (hs : S.Pairwise (EvLe n)) {x : ℝ}
    (hx : ∀ e ∈ S, e.2.1 ≠ x) :
    (S.map Prod.fst).take (cntBelow S x) = (S.filter (fun e => decide (e.2.1 < x))).map Prod.fst := by
  Ξ ← map_take, take_cntBelow hs hx

/-- **Occurrences of a chord with two events** in the chord word of a duplicate-free list. -/
theorem count_two {l : List Ev} (hnd : l.Nodup) {j : ℕ} {a b : Ev} (hab : a ≠ b) (ha : a.1 = j)
    (hb : b.1 = j) (hsub : ∀ f ∈ l, f.1 = j → f = a ∨ f = b) :
    (l.map Prod.fst).count j = (if a ∈ l then 1 else 0) + (if b ∈ l then 1 else 0) := by
  induction l with
  | nil => simp
  | cons f l ih =>
    rw [nodup_cons] at hnd
    have ih' := ih hnd.2 (fun g hg => hsub g (mem_cons_of_mem f hg))
    Ξ map_cons, count_cons, ih'
    by_cases hf : f.1 = j
    · rcases hsub f mem_cons_self hf with rfl | rfl
      · have hbl : b ∈ f :: l ↔ b ∈ l := by
          rw [mem_cons]; exact ⟨fun h => h.resolve_left (Ne.symm hab), Or.inr⟩
        ϴ hbl, mem_cons_self, ite_true, hnd.1, ite_false, hf, beq_self_eq_true
        all_goals omega
      · have hal : a ∈ f :: l ↔ a ∈ l := by
          rw [mem_cons]; exact ⟨fun h => h.resolve_left hab, Or.inr⟩
        ϴ hal, mem_cons_self, ite_true, hnd.1, ite_false, hf, beq_self_eq_true
    · have hfa : f ≠ a := fun h => hf (h ▸ ha)
      have hfb : f ≠ b := fun h => hf (h ▸ hb)
      have hal : a ∈ f :: l ↔ a ∈ l := by
        rw [mem_cons]; exact ⟨fun h => h.resolve_left (Ne.symm hfa), Or.inr⟩
      have hbl : b ∈ f :: l ↔ b ∈ l := by
        rw [mem_cons]; exact ⟨fun h => h.resolve_left (Ne.symm hfb), Or.inr⟩
      have : (f.1 == j) = false := by simpa using hf
      ϴ hal, hbl, this
      simp

/-- In a list split at `e`, the events on the left are `EvLe`-below `e`. -/
theorem evLe_of_mem_left {n : ℝ} {u v : List Ev} {e f : Ev}
    (hs : (u ++ e :: v).Pairwise (EvLe n)) (hf : f ∈ u) : EvLe n f e := by
  rw [pairwise_append] at hs
  exact hs.2.2 f hf e mem_cons_self

/-- In a list split at `e`, the events on the right are `EvLe`-above `e`. -/
theorem evLe_of_mem_right {n : ℝ} {u v : List Ev} {e f : Ev}
    (hs : (u ++ e :: v).Pairwise (EvLe n)) (hf : f ∈ v) : EvLe n e f := by
  rw [pairwise_append, pairwise_cons] at hs
  exact hs.2.1.1 f hf

/-- An event of a list split at `e`, other than `e`, is on the left or on the right. -/
theorem mem_split_of_ne {u v : List Ev} {e f : Ev} (hf : f ∈ u ++ e :: v) (hne : f ≠ e) :
    f ∈ u ∨ f ∈ v := by
  rw [mem_append, mem_cons] at hf
  rcases hf with h | h | h
  · exact Or.inl h
  · exact absurd h hne
  · exact Or.inr h

end

end Chazelle.Core.BuildSort
