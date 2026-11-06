module

public import Chazelle.Golf

public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Infix
public import Mathlib.Order.Basic
public import Mathlib.Data.List.GetD

/-!
# WP-C (BuildNF): the stack pass over a parenthesis word

`BuildNF` sorts the `2K` attachment events of the chords along the walk; reading the sorted events
as chord indices gives a word `w` in which every chord occurs twice.  The tie fact
(`Chazelle.Core.FactsTie`) and the absence of crossings (`WalkAx.no_cross`) make `w` a
**parenthesis word**: no pattern `i … j … i … j` with `i ≠ j` (`NoCross`).  This file is the
abstract algorithm run on `w`:

* `step st x`: pop if `x` is on top of the stack, push otherwise; `run u` folds it over `u`;
* `openList u`: the chords open after the prefix `u` (exactly one occurrence), latest first.

## Results

* `run_eq_openList`: on every prefix of a parenthesis word, the stack is `openList` of the prefix
  (so a closing event always finds its chord on top: the pass never pops a wrong chord);
* `run_eq_nil`: after the whole word the stack is empty;
* `openList_snoc_open`, `openList_snoc_close`: an opening event pushes, a closing one pops;
* `label_eq_iff`: two gaps of the word (after the prefixes of lengths `m` and `m'`) get the same
  label (top of the stack, `none` for the root region) iff every chord is open at both or at
  neither — i.e. iff no chord separates them.  Together with the cut structure (two non-cut
  positions face the same region iff no chord separates their keys) this identifies the regions
  of the submap with the labels.
-/

namespace Chazelle.Core.BuildStack

@[expose] public section

open List

/-- One step of the stack pass: pop if `x` is on top, push otherwise. -/
def step (st : List ℕ) (x : ℕ) : List ℕ := if st.head? = some x then st.tail else x :: st

/-- The stack after reading `u`. -/
def run (u : List ℕ) : List ℕ := u.foldl step []

/-- The chords open after `u` (exactly one occurrence in `u`), the latest opened first. -/
def openList (u : List ℕ) : List ℕ := u.reverse.filter (fun x => decide (u.count x = 1))

/-- Every letter of `w` occurs exactly twice. -/
def Twice (w : List ℕ) : Prop := ∀ x ∈ w, w.count x = 2

/-- **A parenthesis word**: no pattern `i … j … i … j` with `i ≠ j`. -/
def NoCross (w : List ℕ) : Prop := ∀ i j, i ≠ j → ¬ [i, j, i, j] <+ w

/-- The label of the gap after the first `m` letters: the innermost open chord (`none`: the root
region). -/
def label (w : List ℕ) (m : ℕ) : Option ℕ := (run (w.take m)).head?

theorem run_snoc (u : List ℕ) (x : ℕ) : run (u ++ [x]) = step (run u) x := by
  Θ run, List.foldl_append

theorem mem_openList {u : List ℕ} {x : ℕ} : x ∈ openList u ↔ u.count x = 1 := by
  unfold openList
  Ξ mem_filter, mem_reverse, decide_eq_true_iff
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨count_pos_iff.1 (⋄), h⟩

/-- **An opening event pushes.** -/
theorem openList_snoc_open {u : List ℕ} {x : ℕ} (hx : u.count x = 0) :
    openList (u ++ [x]) = x :: openList u := by
  unfold openList
  rw [reverse_append, reverse_singleton, singleton_append, filter_cons,
    ite_eq_left (⊚ count_append, hx)]
  congr 1
  apply filter_congr
  intro y hy
  have hyx : y ≠ x := by
    rintro rfl
    rw [mem_reverse] at hy
    exact absurd (count_pos_iff.2 hy) (⋄)
  Θ count_append, Ne.symm hyx

/-- **A closing event pops**: if `x` occurs once in `u` and is the latest open chord, reading it
again removes it. -/
theorem openList_snoc_close {u : List ℕ} {x : ℕ} {rest : List ℕ} (hx : u.count x = 1)
    (hlist : openList u = x :: rest) : openList (u ++ [x]) = rest := by
  have hxu : x ∈ u.reverse := by rw [mem_reverse]; exact count_pos_iff.1 (⋄)
  obtain ⟨a, b, hab⟩ := List.append_of_mem hxu
  have hcnt : u.reverse.count x = 1 := by rw [count_reverse]; exact hx
  rw [hab, count_append, count_cons_self] at hcnt
  have hxa : x ∉ a := fun h => by have := count_pos_iff.2 h; omega
  have hxb : x ∉ b := fun h => by have := count_pos_iff.2 h; omega
  unfold openList at hlist ⊢
  rw [hab, filter_append, filter_cons, ite_eq_left (by simpa using hx)] at hlist
  -- the part before `x` contributes nothing
  have ha : a.filter (fun y => decide (u.count y = 1)) = [] := by
    rcases hfa : a.filter (fun y => decide (u.count y = 1)) with _ | ⟨z, zs⟩
    · rfl
    · exfalso
      rw [hfa, cons_append, cons.injEq] at hlist
      have hz : z ∈ a := mem_of_mem_filter (by rw [hfa]; exact mem_cons_self)
      exact hxa (hlist.1 ▸ hz)
  rw [ha, nil_append, cons.injEq] at hlist
  rw [reverse_append, reverse_singleton, singleton_append, filter_cons,
    ite_eq_right (⊚ count_append, hx), hab, filter_append, filter_cons,
    ite_eq_right (⊚ count_append, hx), ← hlist.2]
  have hcongr : ∀ l : List ℕ, x ∉ l →
      l.filter (fun y => decide ((u ++ [x]).count y = 1)) =
        l.filter (fun y => decide (u.count y = 1)) := by
    intro l hl
    apply filter_congr
    intro y hy
    have hyx : y ≠ x := fun h => hl (h ▸ hy)
    Θ count_append, Ne.symm hyx
  Ξ hcongr a hxa, hcongr b hxb, ha, nil_append

/-- The latest open chord of a prefix, when the next letter closes a chord: in a parenthesis
word, it is that chord. -/
theorem head_openList {w u v : List ℕ} (htw : Twice w) (hnc : NoCross w) {x : ℕ}
    (hw : w = u ++ [x] ++ v) (hx : u.count x = 1) : ∃ rest, openList u = x :: rest := by
  have hxo : x ∈ openList u := mem_openList.2 hx
  rcases hlist : openList u with _ | ⟨y, rest⟩
  · rw [hlist] at hxo; exact absurd hxo not_mem_nil
  · refine ⟨rest, ?_⟩
    by_contra hne
    have hyx : y ≠ x := fun h => hne (Ρ h)
    have hxr : x ∈ rest := by
      rw [hlist, mem_cons] at hxo
      exact hxo.resolve_left (Ne.symm hyx)
    have hy1 : u.count y = 1 := mem_openList.1 (by rw [hlist]; exact mem_cons_self)
    -- `x` then `y` in `u`
    have h1 : [y, x] <+ u.reverse := by
      have : [y, x] <+ openList u := by
        rw [hlist]; exact (singleton_sublist.2 hxr).cons_cons y
      exact this.trans filter_sublist
    have h1' : [x, y] <+ u := by simpa using h1.reverse
    -- `y` occurs again after the current `x`
    have hyw : w.count y = 2 := htw y (by rw [hw]; simp [count_pos_iff.1 (by omega : 0 < u.count y)])
    have hyv : y ∈ v := by
      rw [hw, count_append, count_append,
        count_eq_zero_of_not_mem (by simp [hyx] : y ∉ [x])] at hyw
      exact count_pos_iff.1 (⋄)
    have h2 : [x, y] <+ [x] ++ v := (singleton_sublist.2 hyv).cons_cons x
    exact hnc x y (Ne.symm hyx) (by rw [hw, append_assoc]; exact h1'.append h2)

/-- **The stack is the list of open chords** on every prefix of a parenthesis word. -/
theorem run_eq_openList {w : List ℕ} (htw : Twice w) (hnc : NoCross w) :
    ∀ {u : List ℕ}, u <+: w → run u = openList u := by
  intro u
  induction u using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton u x ih =>
    intro hu
    obtain ⟨v, hv⟩ := hu
    have ih' := ih ⟨[x] ++ v, Ρ ← hv, append_assoc⟩
    Ξ run_snoc, ih'
    have hxw : w.count x = 2 := htw x (by rw [← hv]; simp)
    have hcx : u.count x ≤ 1 := by
      rw [← hv, count_append, count_append, count_singleton_self] at hxw; omega
    rcases Nat.lt_or_ge (u.count x) 1 with h0 | h1
    · have h0' : u.count x = 0 := ⋄
      Ξ openList_snoc_open h0'
      unfold step
      Ξ ite_eq_right
      intro h
      have := mem_openList.1 (mem_of_mem_head? h)
      omega
    · have h1' : u.count x = 1 := ⋄
      obtain ⟨rest, hrest⟩ := head_openList htw hnc (hv.symm.trans (Ρ append_assoc)) h1'
      Ξ openList_snoc_close h1' hrest, hrest
      unfold step
      simp

/-- **The stack is empty at the end** of a parenthesis word. -/
theorem run_eq_nil {w : List ℕ} (htw : Twice w) (hnc : NoCross w) : run w = [] := by
  Ξ run_eq_openList htw hnc (prefix_refl w)
  unfold openList
  Ξ filter_eq_nil_iff
  intro x hx
  rw [mem_reverse] at hx
  Θ htw x hx

/-- The label of a gap is the head of the open list. -/
theorem label_eq {w : List ℕ} (htw : Twice w) (hnc : NoCross w) (m : ℕ) :
    label w m = (openList (w.take m)).head? := by
  unfold label
  Ξ run_eq_openList htw hnc (take_prefix m w)

/-- Equal open sets give equal open lists (for two prefixes of one word). -/
theorem openList_eq_of_prefix {u u' : List ℕ} (h : u <+: u')
    (hiff : ∀ i, (u.count i = 1 ↔ u'.count i = 1)) : openList u = openList u' := by
  obtain ⟨v, rfl⟩ := h
  unfold openList
  Ξ reverse_append, filter_append
  have hv : v.reverse.filter (fun x => decide ((u ++ v).count x = 1)) = [] := by
    Ξ filter_eq_nil_iff
    intro x hx h
    rw [mem_reverse] at hx
    simp only [decide_eq_true_eq] at h
    have h2 := (hiff x).2 h
    rw [count_append] at h
    have := count_pos_iff.2 hx
    omega
  Ξ hv, nil_append
  apply filter_congr
  intro y _
  ϴ hiff y

/-- If `j` is open after `u` and below the latest open chord `i`, then `j` occurs before `i` in
`u`. -/
theorem sublist_of_openList {u : List ℕ} {i j : ℕ} {rest : List ℕ} (h : openList u = i :: rest)
    (hj : j ∈ rest) : [j, i] <+ u := by
  have : [i, j] <+ u.reverse := by
    have : [i, j] <+ openList u := by rw [h]; exact (singleton_sublist.2 hj).cons_cons i
    exact this.trans filter_sublist
  simpa using this.reverse

/-- One direction of `label_eq_iff`, for a chord open at `m` but not at `m'`. -/
theorem label_ne_aux {w : List ℕ} (htw : Twice w) (hnc : NoCross w) {m m' : ℕ} {j : ℕ}
    (hj : (w.take m).count j = 1) (hj' : (w.take m').count j ≠ 1) :
    (openList (w.take m)).head? ≠ (openList (w.take m')).head? := by
  intro heq
  have hjo : j ∈ openList (w.take m) := mem_openList.2 hj
  rcases hl : openList (w.take m) with _ | ⟨i, rest⟩
  · rw [hl] at hjo; exact not_mem_nil hjo
  rw [hl] at heq
  rcases hl' : openList (w.take m') with _ | ⟨i', rest'⟩
  · rw [hl'] at heq; simp at heq
  rw [hl', head?_cons, head?_cons, Option.some.injEq] at heq
  subst heq
  have hi' : (w.take m').count i = 1 := mem_openList.1 (by rw [hl']; exact mem_cons_self)
  have hji : j ≠ i := by rintro rfl; exact hj' hi'
  have hjr : j ∈ rest := by
    rw [hl, mem_cons] at hjo; exact hjo.resolve_left hji
  have hsub := sublist_of_openList hl hjr
  have hi1 : (w.take m).count i = 1 := mem_openList.1 (by rw [hl]; exact mem_cons_self)
  rcases le_total m' m with hle | hle
  · -- `m' ≤ m`: `j` does not occur before `m'`, but `i` does, and `j` precedes `i`
    obtain ⟨z, hz⟩ : ∃ z, w.take m = w.take m' ++ z :=
      ⟨(w.drop m').take (m - m'), Ρ ← List.take_add, Nat.add_sub_cancel' hle⟩
    have hj0 : (w.take m').count j = 0 := by
      rw [hz, count_append] at hj; omega
    rw [hz, count_append, hi'] at hi1
    rw [hz] at hsub
    obtain ⟨l1, l2, heq, h1, h2⟩ := List.sublist_append_iff.1 hsub
    rcases l1 with _ | ⟨a, l1⟩
    · rw [nil_append] at heq
      have : i ∈ z := h2.subset (by rw [← heq]; simp)
      have := count_pos_iff.2 this
      omega
    · rw [cons_append, cons.injEq] at heq
      have : j ∈ w.take m' := h1.subset (by rw [← heq.1]; exact mem_cons_self)
      have := count_pos_iff.2 this
      omega
  · -- `m ≤ m'`: `j` closes between `m` and `m'`, `i` after `m'`: a crossing
    obtain ⟨z, hz⟩ : ∃ z, w.take m' = w.take m ++ z :=
      ⟨(w.drop m).take (m' - m), Ρ ← List.take_add, Nat.add_sub_cancel' hle⟩
    have hiz : z.count i = 0 := by rw [hz, count_append, hi1] at hi'; omega
    have hjz : j ∈ z := by
      rw [hz, count_append, hj] at hj'
      exact count_pos_iff.1 (⋄)
    have hiw : w.count i = 2 := htw i (mem_of_mem_take (count_pos_iff.1 (by omega : 0 < (w.take m).count i)))
    have hw : w = w.take m ++ z ++ w.drop m' := Ρ ← hz, take_append_drop
    have hiy : i ∈ w.drop m' := by
      rw [hw, count_append, count_append, hi1, hiz] at hiw
      exact count_pos_iff.1 (⋄)
    have h2 : [j] ++ [i] <+ z ++ w.drop m' :=
      (singleton_sublist.2 hjz).append (singleton_sublist.2 hiy)
    exact hnc j i hji (by rw [hw, append_assoc]; exact hsub.append h2)

/-- **Two gaps get the same label iff no chord separates them** (every chord is open at both or
at neither). -/
theorem label_eq_iff {w : List ℕ} (htw : Twice w) (hnc : NoCross w) (m m' : ℕ) :
    label w m = label w m' ↔ ∀ i, ((w.take m).count i = 1 ↔ (w.take m').count i = 1) := by
  Ξ label_eq htw hnc, label_eq htw hnc
  constructor
  · intro h i
    by_contra hne
    by_cases hA : (w.take m).count i = 1
    · have hB : (w.take m').count i ≠ 1 := fun hB => hne ⟨fun _ => hB, fun _ => hA⟩
      exact label_ne_aux htw hnc hA hB h
    · have hB : (w.take m').count i = 1 := by
        by_contra hB; exact hne ⟨fun h' => absurd h' hA, fun h' => absurd h' hB⟩
      exact label_ne_aux htw hnc hB hA h.symm
  · intro h
    rcases le_total m m' with hle | hle
    · obtain ⟨z, hz⟩ : ∃ z, w.take m' = w.take m ++ z :=
        ⟨(w.drop m).take (m' - m), Ρ ← List.take_add, Nat.add_sub_cancel' hle⟩
      Ξ openList_eq_of_prefix ⟨z, hz.symm⟩ h
    · obtain ⟨z, hz⟩ : ∃ z, w.take m = w.take m' ++ z :=
        ⟨(w.drop m').take (m - m'), Ρ ← List.take_add, Nat.add_sub_cancel' hle⟩
      Ξ openList_eq_of_prefix ⟨z, hz.symm⟩ (fun i => (h i).symm)

end

end Chazelle.Core.BuildStack
