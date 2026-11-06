/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count

/-!
# Lists: entries with a default, blocks, sums, counting, sorted lists

General facts about lists. Arrays are lists here, and entry `i` of a list is `l.getD i d`. The
sections:

* Entries with a default: `getD` of a list that was appended to, cut, tabulated, mapped or changed
  in one place.
* Blocks: `(List.range n).flatMap f` puts the blocks `f 0, …, f (n - 1)` one after the other. Where
  an entry of a block stands, for blocks of any lengths and for blocks of one length.
* Sums: partial sums, the triangle inequality, and the sum over a list that enumerates the image of
  a finite set.
* A running minimum.
* Counting: how often a value occurs among the first entries of a list, or among the values of a
  function on `Fin n`; the list of the `j < n` with a property.
* Sorted lists: what `dropWhile` and `takeWhile` leave of a strictly increasing list; first
  occurrences in a weakly increasing list.
* Two notions of this project: `AbsLe l U` says that all members of `l` have absolute value at most
  `U`, and `sumLists` is the entrywise sum of lists of one length.
-/


namespace List

variable {α β : Type*}

variable {l : List α}

/-! ## Entries with a default -/

/-- What holds for the default and for every member of a list holds for every `getD`. -/
theorem getD_of_forall_mem {p : α → Prop} {d : α} (hd : p d) (h : ∀ x ∈ l, p x)
    (i : ℕ) : p (l.getD i d) := by
  grind

/-- Entry `j` of the second of two lists put together. -/
theorem getD_append_add (l l' : List α) (j : ℕ) (d : α) :
    (l ++ l').getD (l.length + j) d = l'.getD j d := by
  grind


variable {n j : ℕ}

/-- Entry `j < n` of the first `n` entries. -/
theorem getD_take_of_lt (l : List α) (hj : j < n) (d : α) :
    (l.take n).getD j d = l.getD j d := by
  simp_all

variable {i : ℕ}

/-- Entry `i < n` of the table `f 0, …, f (n - 1)`. -/
theorem getD_map_range (f : ℕ → α) (hi : i < n) (d : α) :
    ((List.range n).map f).getD i d = f i := by
  simp_all

/-- Entry `i < l.length` of `l.map f`, whatever the two defaults. Mathlib's `List.getD_map` is for
all `i`, with the default `f d`. -/
theorem getD_map_of_lt (f : α → β) (hi : i < l.length) (d : α) (d' : β) :
    (l.map f).getD i d' = f (l.getD i d) := by
  simp_all

/-- The entries of a list in which entry `q < l.length` was replaced by `a`. -/
theorem getD_set_of_lt {q : ℕ} (hq : q < l.length) (a d : α) (q' : ℕ) :
    (l.set q a).getD q' d = if q' = q then a else l.getD q' d := by
  grind

/-- One more member at the end changes the entry number `l.length` only. -/
theorem getD_append_singleton (l : List α) (a d : α) :
    (fun e => (l ++ [a]).getD e d) = Function.update (fun e => l.getD e d) l.length a := by
  grind

/-- The first `i + 1` entries are the first `i` entries and entry `i`. -/
theorem take_succ_getD (l : List α) (hi : i < l.length) (d : α) :
    l.take (i + 1) = l.take i ++ [l.getD i d] := by
  simp_all

variable {r : ℕ}

variable (f : ℕ → List α)

/-! ## Blocks one after the other -/

/-- Blocks of any lengths: entry `o` of block `r` stands after the blocks `0, …, r - 1`. -/
theorem getD_flatMap_range_sum {o : ℕ} (hr : r < n) (ho : o < (f r).length)
    (d : α) :
    ((List.range n).flatMap f).getD (((List.range r).map fun s => (f s).length).sum + o) d =
      (f r).getD o d := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hr
  rw [Nat.add_assoc, List.range_add, List.flatMap_append, ← List.length_flatMap, getD_append_add,
    Nat.add_comm, List.range_add, List.map_append, List.flatMap_append,
    List.getD_append _ _ _ _ (by simp_all)]
  simp

variable {k : ℕ}

/-- The length of `n` blocks of length `k`. -/
theorem length_flatMap_range (n : ℕ) (f : ℕ → List α) (hf : ∀ z < n, (f z).length = k) :
    ((List.range n).flatMap f).length = n * k := by
  simp_all [List.length_flatMap, List.map_congr_left]

/-- Blocks of length `k`: entry `r` of block `z` has the index `z * k + r`. -/
theorem getD_flatMap_range (hf : ∀ z < n, (f z).length = k) {z : ℕ}
    (hz : z < n) (hr : r < k) (d : α) :
    ((List.range n).flatMap f).getD (z * k + r) d = (f z).getD r d := by
  rw [← length_flatMap_range z f fun s hs => by grind, List.length_flatMap]
  grind [getD_flatMap_range_sum]

/-- A run of `n` blocks, cut out of a list of blocks of length `k`. -/
theorem take_drop_flatMap_range (m n c : ℕ) (f : ℕ → List α)
    (hf : ∀ z < m + n + c, (f z).length = k) :
    (((List.range (m + n + c)).flatMap f).drop (m * k)).take (n * k) =
      (List.range n).flatMap fun z => f (m + z) := by
  have hm : ((List.range m).flatMap f).length = m * k :=
    by grind [length_flatMap_range]
  have hn : ((List.range n).flatMap fun z => f (m + z)).length = n * k :=
    by grind [length_flatMap_range]
  grind [List.range_add, List.append_assoc, List.flatMap_map, List.drop_left, List.take_left]

/-- An entrywise operation on two lists of blocks of one length works block by block. -/
theorem zipWith_flatMap_range {γ : Type*} (g : α → β → γ) (n : ℕ) (f : ℕ → List α)
    (f' : ℕ → List β) (hf : ∀ z, (f z).length = k) (hf' : ∀ z, (f' z).length = k) :
    List.zipWith g ((List.range n).flatMap f) ((List.range n).flatMap f') =
      (List.range n).flatMap fun z => List.zipWith g (f z) (f' z) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlen : ((List.range n).flatMap f).length = ((List.range n).flatMap f').length := by
      simp_all
    grind [List.range_succ]

variable {M : Type*}

/-! ## Sums -/

/-- The sum of the table `f 0, …, f (n - 1)` is the sum over `Finset.range n`. For a sum over
`Fin n` go on with `Finset.sum_range`. -/
theorem sum_map_range [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i :=
  rfl

/-- Partial sums of natural numbers grow. -/
theorem sum_map_range_mono (g : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) :
    ((List.range a).map g).sum ≤ ((List.range b).map g).sum := by
  grind [Nat.exists_eq_add_of_le, List.range_add]

/-- One more term of a partial sum; beyond the end of the list the term is `0`. Within the list,
`List.sum_take_succ` has `l[j]` in place of `l.getD j 0`. -/
theorem sum_take_succ_getD [AddMonoid M] (l : List M) (j : ℕ) :
    (l.take (j + 1)).sum = (l.take j).sum + l.getD j 0 := by
  rcases j.lt_or_ge l.length with hj | hj
  · simp_all
  grind [List.getD_eq_default, List.take_of_length_le, Nat.le_succ_of_le, add_zero]

/-- One more term of a partial sum of the table `f 0, …, f (n - 1)`. -/
theorem sum_take_map_range_succ [AddMonoid M] (f : ℕ → M) (hj : j < n) :
    (((List.range n).map f).take (j + 1)).sum = (((List.range n).map f).take j).sum + f j := by
  simp_all

section

variable {R : Type*} [AddCommGroup R] [LinearOrder R] [IsOrderedAddMonoid R]

/-- The triangle inequality for the sum of a list. -/
theorem abs_sum_le_sum_abs (l : List R) : |l.sum| ≤ (l.map fun x => |x|).sum :=
  Multiset.abs_sum_le_sum_abs (s := (l : Multiset R))

/-- The sum of an initial part of a list is at most the sum of the absolute values of the whole
list, in absolute value. -/
theorem abs_sum_take_le_sum_abs (l : List R) (k : ℕ) :
    |(l.take k).sum| ≤ (l.map fun x => |x|).sum := by
  apply (abs_sum_le_sum_abs _).trans
  refine Sublist.sum_le_sum (by grind) fun a ha => ?_
  aesop

end

variable {B : ℤ}

/-- If `|f x| ≤ B` for all `x ∈ l`, then every initial part of the numbers `f x` has a sum of
absolute value at most `l.length * B`. -/
theorem abs_sum_take_map_le (l : List α) (f : α → ℤ) (h : ∀ x ∈ l, |f x| ≤ B) (k : ℕ) :
    |((l.map f).take k).sum| ≤ l.length * B := by
  apply (List.abs_sum_take_le_sum_abs _ k).trans
  simpa using List.sum_le_card_nsmul ((l.map f).map fun x => |x|) B (by simp_all)

/-- If `|f x| ≤ B` for all `x ∈ l`, then `|(l.map f).sum| ≤ l.length * B`. -/
theorem abs_sum_map_le (l : List α) (f : α → ℤ) (h : ∀ x ∈ l, |f x| ≤ B) :
    |(l.map f).sum| ≤ l.length * B := by
  have htake := abs_sum_take_map_le l f h l.length
  grind [List.length_map, List.take_length]

/-- If `l` has no repetitions, every member of `l` is `g x` for some `x ∈ S`, `g` is injective and
`l` has as many members as `S` has elements, then the members of `l` are exactly the `g x` with
`x ∈ S`. -/
theorem toFinset_eq_image_of_length_eq_card [DecidableEq β] (l : List β) (hl : l.Nodup)
    (S : Finset α) (g : α → β)
    (hinj : Function.Injective g) (hsub : ∀ y ∈ l, ∃ x ∈ S, g x = y) (hcard : l.length = S.card) :
    l.toFinset = S.image g := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => ?_) ?_
  · simp_all
  grind [Finset.card_image_of_injective, List.toFinset_card_of_nodup]

/-- Under the same hypotheses, a sum over `l` is a sum over `S`. -/
theorem sum_map_eq_sum_of_length_eq_card [AddCommMonoid M] (l : List β) (hl : l.Nodup)
    (S : Finset α)
    (g : α → β) (hinj : Function.Injective g) (hsub : ∀ y ∈ l, ∃ x ∈ S, g x = y)
    (hcard : l.length = S.card) (F : β → M) : (l.map F).sum = ∑ x ∈ S, F (g x) := by
  classical
  rw [← List.sum_toFinset F hl, toFinset_eq_image_of_length_eq_card l hl S g hinj hsub hcard,
    Finset.sum_image fun x _ y _ hxy => hinj hxy]

/-! ## A running minimum -/

/-- A running minimum over `f 0, …, f m` is a lower bound of these values. -/
theorem foldl_min_le [LinearOrder β] (f : ℕ → β) (m : ℕ) (hk : k ≤ m) :
    (List.range m).foldl (fun acc j => min acc (f (j + 1))) (f 0) ≤ f k := by
  induction m with
  | zero => simp_all
  | succ m ih =>
    grind [List.range_succ]

/-- A running minimum over `f 0, …, f m` is one of these values. -/
theorem exists_foldl_min_eq [LinearOrder β] (f : ℕ → β) (m : ℕ) :
    ∃ k ≤ m, (List.range m).foldl (fun acc j => min acc (f (j + 1))) (f 0) = f k := by
  induction m with
  | zero => simp
  | succ m ih =>
    grind [List.range_succ]

/-! ## Counting -/

/-- A count among the first `i + 1` entries, from the count among the first `i` and entry `i`. -/
theorem count_take_succ [DecidableEq α] (l : List α) (x : α)
    (hi : i < l.length) :
    (l.take (i + 1)).count x = (l.take i).count x + if l[i] = x then 1 else 0 := by
  grind [List.take_succ_eq_append_getElem, List.count_singleton]

/-- A count among the first `i + 1` entries, with entry `i` read by `getD`. -/
theorem count_take_succ_getD [DecidableEq α] (l : List α) (x : α) (hi : i < l.length)
    (d : α) :
    (l.take (i + 1)).count x = (l.take i).count x + if l.getD i d = x then 1 else 0 := by
  grind [List.count_take_succ, List.getD_eq_getElem]

/-- If entry `i < l.length` is `x`, then `x` occurs less often before place `i` than in the whole
list. -/
theorem count_take_lt [DecidableEq α] {x : α} (hi : i < l.length) (d : α)
    (hx : l.getD i d = x) : (l.take i).count x < l.count x := by
  have hle : (l.take (i + 1)).count x ≤ l.count x := by grind [List.take_sublist]
  rw [count_take_succ_getD l x hi, if_pos hx] at hle
  omega

/-- The members with `t a < z + 1` are those with `t a < z` and those with `t a = z`. -/
theorem length_filter_lt_succ (t : α → ℕ) (z : ℕ) (l : List α) :
    (l.filter fun a => decide (t a < z + 1)).length =
      (l.filter fun a => decide (t a < z)).length +
        (l.filter fun a => decide (t a = z)).length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    grind

variable (q : ℕ → Prop)

/-- The list of the `j < n` with `q j` has `Nat.count q n` members. -/
theorem length_filter_range [DecidablePred q] (n : ℕ) :
    ((List.range n).filter fun j => decide (q j)).length = Nat.count q n := by
  grind [Nat.count]

/-- In the increasing list of the `j < n` with `q j`, the member `i` has the number
`Nat.count q i`. -/
theorem getD_filter_range_count [DecidablePred q] (n : ℕ)
    (hi : i < n) (hq : q i) :
    ((List.range n).filter fun j => decide (q j)).getD (Nat.count q i) 0 = i := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [List.range_succ, List.filter_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h | rfl
    · rw [List.getD_append _ _ _ _ (by
        rw [List.length_filter_range]
        exact (Nat.count_lt_count_succ_iff.2 hq).trans_le (Nat.count_monotone q h))]
      omega
    grind [List.getD_append_right, List.length_filter_range]

/-- How often a value occurs among the first `i` values of a function on `Fin n`. -/
theorem count_take_ofFn [DecidableEq α] (f : Fin n → α) (a : α) (i : ℕ) :
    ((List.ofFn f).take i).count a =
      (Finset.univ.filter fun j : Fin n => (j : ℕ) < i ∧ f j = a).card := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    cases i with
    | zero => simp
    | succ i =>
      grind [List.ofFn_succ, Finset.card_filter, Fin.sum_univ_succ, add_comm]

/-- How often a value occurs in the table of a function on `Fin n`. -/
theorem count_ofFn [DecidableEq α] (f : Fin n → α) (a : α) :
    (List.ofFn f).count a = (Finset.univ.filter fun i => f i = a).card := by
  simpa [List.take_of_length_le] using count_take_ofFn f a n

/-! ## Sorted lists -/

section Sorted

variable [LinearOrder α]

/-- In a weakly increasing list, an entry that is the first or differs from its predecessor has not
occurred before. -/
theorem getD_notMem_take_of_sorted {l : List α} (hs : l.Pairwise (· ≤ ·)) {i : ℕ}
    (hi : i < l.length)
    (d : α) (h : i = 0 ∨ l.getD i d ≠ l.getD (i - 1) d) : l.getD i d ∉ l.take i := by
  grind [List.mem_iff_getElem, List.pairwise_iff_getElem, Nat.lt_or_ge]

end Sorted

end List

namespace ThreeSumApsp

/-! ## Lists of integers that are bounded in absolute value -/

/-- All members of the list `l` have absolute value at most `U`. -/
def AbsLe (l : List ℤ) (U : ℤ) : Prop := ∀ x ∈ l, |x| ≤ U

variable {l : List ℤ} {U : ℤ}

/-- A bound on the absolute values of all members bounds every entry. -/
theorem AbsLe.getElem (h : AbsLe l U) {i : ℕ} (hi : i < l.length) :
    |l[i]| ≤ U :=
  by aesop

/-- A bound on the absolute values of all members bounds every `getD` with default `0`. -/
theorem AbsLe.abs_getD_le (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  List.getD_of_forall_mem (by assumption) h i

/-! ## The entrywise sum of lists -/
