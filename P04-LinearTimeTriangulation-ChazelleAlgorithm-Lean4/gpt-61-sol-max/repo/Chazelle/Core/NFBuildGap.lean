module

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
  all_goals grind

section
variable {n : ℝ} {S : List Ev} (hs : S.Pairwise (EvLe n)) {x : ℝ} (hx : ∀ e ∈ S, e.2.1 ≠ x)
include n hs hx
/-- **The events below a key form a prefix** of a sorted event list. -/
theorem take_cntBelow : S.take (cntBelow S x) = S.filter (fun e => decide (e.2.1 < x)) := by
  induction S with
  | nil => rfl
  | cons e S ih =>
    rw [pairwise_cons] at hs
    have ih' := ih hs.2 (fun f hf => hx f (mem_cons_of_mem e hf))
    unfold cntBelow at ih' ⊢
    grind [Chazelle.Core.BuildSort.EvLe]

/-- The chord word of the events below a key. -/
theorem take_map_cntBelow :
    (S.map Prod.fst).take (cntBelow S x) = (S.filter (fun e => decide (e.2.1 < x))).map Prod.fst := by
  rw [← map_take, take_cntBelow hs hx]


end

/-- **Occurrences of a chord with two events** in the chord word of a duplicate-free list. -/
theorem count_two {l : List Ev} (hnd : l.Nodup) {j : ℕ} {a b : Ev} (hab : a ≠ b) (ha : a.1 = j)
    (hb : b.1 = j) (hsub : ∀ f ∈ l, f.1 = j → f = a ∨ f = b) :
    (l.map Prod.fst).count j = (if a ∈ l then 1 else 0) + (if b ∈ l then 1 else 0) := by
  induction l with
  | nil => simp
  | cons f l ih =>
    grind

section
variable {n : ℝ} {u v : List Ev} {e f : Ev} (hs : (u ++ e :: v).Pairwise (EvLe n))
include u v hs
/-- In a list split at `e`, the events on the left are `EvLe`-below `e`. -/
theorem evLe_of_mem_left (hf : f ∈ u) : EvLe n f e := by
  grind

/-- In a list split at `e`, the events on the right are `EvLe`-above `e`. -/
theorem evLe_of_mem_right (hf : f ∈ v) : EvLe n e f := by
  grind [pairwise_append, pairwise_cons]


end

/-- An event of a list split at `e`, other than `e`, is on the left or on the right. -/
theorem mem_split_of_ne {u v : List Ev} {e f : Ev} (hf : f ∈ u ++ e :: v) (hne : f ≠ e) :
    f ∈ u ∨ f ∈ v := by
  simp_all

end

end Chazelle.Core.BuildSort
