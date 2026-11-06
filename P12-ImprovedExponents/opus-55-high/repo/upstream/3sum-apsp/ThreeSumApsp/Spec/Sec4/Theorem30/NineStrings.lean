/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Range
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Strings of digits with a bounded number of nines (Section 4.2, proofs of Lemma 29, Theorem 30)

All three enumerations of Section 4 come from one: `nineStrs n lo hi`, the strings of n digits
0, …, 9 in which the digit 9 (the digit of P₀) occurs at least lo and at most hi times, in
lexicographic order.

* The boxes with e stars are the leaves with between e and m - t symbols P₀, with their e lowest
  symbols P₀ turned into stars (the proof of Lemma 29).
* The leaves of order below t contributing to an output string η (the paper's w) have, at the m
  levels of its inner set Q, a string with at least m - t + 1 nines (proof of Theorem 30).
* The boxes of η have, at the m levels of Q, a string with exactly m - t nines, the nines being the
  levels of V (Section 4.2).

The file proves what the list contains (`mem_nineStrs`), that it is increasing
(`pairwise_lt_nineStrs`), how long it is (`length_nineStrs`: ∑_f binom(n, f) 9^{n-f}), and how a
routine goes through it: it starts with `nineFirst` (`head?_nineStrs`), and `nineNext` goes from
each string to the next (`nineNext_getElem`); so the string reached after i steps,
`nineStr n lo hi i`, is the member number i (`getElem_nineStrs`).  Read from the right end of the
string, `nineNext` is one pass: skip the positions that cannot be raised, raise one digit
(`nineRaise`), and fill the rest with the least admissible string, zeros followed by nines.  The
proof follows the recursion of the list: the strings with the first digit d form a block,
`nineNext` goes through each block (`nextTo_map_cons`), and from the last string of a block to the
first string of the next block (`head_nineBlocks`).
-/


namespace ThreeSumApsp.Spec

/-- The strings of n digits below 10 with between lo and hi digits 9, in lexicographic order. -/
def nineStrs : ℕ → ℕ → ℕ → List (List ℕ)
  | 0, lo, _ => if lo = 0 then [[]] else []
  | n + 1, lo, hi =>
    (List.range 9).flatMap (fun d => (nineStrs n lo hi).map (d :: ·)) ++
      (if hi = 0 then [] else (nineStrs n (lo - 1) (hi - 1)).map (9 :: ·))

/-- The least string of n digits with at least lo digits 9: zeros, then lo nines. -/
def nineFirst (n lo : ℕ) : List ℕ := List.replicate (n - lo) 0 ++ List.replicate lo 9

/-- The first digit d raised by one, if that is possible, and the least admissible string of n
digits behind it. -/
def nineRaise (lo hi n d : ℕ) : Option (List ℕ) :=
  if d < 8 then some ((d + 1) :: nineFirst n lo)
  else if d = 8 ∧ 0 < hi then some (9 :: nineFirst n (lo - 1))
  else none

/-- The string after l, or none if l is the last one: the rest of the string goes to the string
after it, or, if it is the last one, the first digit is raised. -/
def nineNext : ℕ → ℕ → List ℕ → Option (List ℕ)
  | _, _, [] => none
  | lo, hi, d :: l =>
    match nineNext (if d = 9 then lo - 1 else lo) (if d = 9 then hi - 1 else hi) l with
    | some l' => some (d :: l')
    | none => nineRaise lo hi l.length d

/-- The string number i of the list, as a routine reaches it: from the first string by going to the
next one i times. -/
def nineStr (n lo hi i : ℕ) : List ℕ := (fun l => (nineNext lo hi l).getD l)^[i] (nineFirst n lo)

variable {l : List ℕ}

/-! ## The members of the list -/

/-- The first digit is below 9, or it is a 9 and counts. -/
theorem cons_mem_nineStrs {n lo hi d : ℕ} :
    d :: l ∈ nineStrs (n + 1) lo hi ↔
      (d < 9 ∧ l ∈ nineStrs n lo hi) ∨ (d = 9 ∧ hi ≠ 0 ∧ l ∈ nineStrs n (lo - 1) (hi - 1)) := by
  grind [nineStrs]

theorem mem_nineStrs {n lo hi : ℕ} (l : List ℕ) :
    l ∈ nineStrs n lo hi ↔
      l.length = n ∧ (∀ d ∈ l, d < 10) ∧ lo ≤ l.count 9 ∧ l.count 9 ≤ hi := by
  induction n generalizing lo hi l with
  | zero => grind [nineStrs]
  | succ n ih =>
    rcases l with _ | ⟨d, l⟩
    · simp [nineStrs]
    rw [cons_mem_nineStrs, List.forall_mem_cons]
    grind

theorem length_of_mem_nineStrs {n lo hi : ℕ} (hl : l ∈ nineStrs n lo hi) :
    l.length = n :=
  by grind [mem_nineStrs]

/-- The digit of the star does not occur. -/
theorem ten_notMem_of_mem_nineStrs {n lo hi : ℕ} (hl : l ∈ nineStrs n lo hi) :
    10 ∉ l :=
  by grind [mem_nineStrs, lt_irrefl]

/-- There is no string with more nines than digits, or if the bounds contradict each other. -/
theorem nineStrs_eq_nil {n lo hi : ℕ} (h : n < lo ∨ hi < lo := by omega) : nineStrs n lo hi = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  grind [mem_nineStrs]

/-- The list is strictly increasing in the lexicographic order. -/
theorem pairwise_lt_nineStrs (n lo hi : ℕ) : (nineStrs n lo hi).Pairwise (· < ·) := by
  induction n generalizing lo hi with
  | zero =>
    grind [nineStrs]
  | succ n ih =>
    grind [nineStrs, List.pairwise_lt_range, List.cons_lt_cons_iff]

theorem nineStrs_nodup (n lo hi : ℕ) : (nineStrs n lo hi).Nodup :=
  (pairwise_lt_nineStrs n lo hi).imp fun h => ne_of_lt h

/-! ## The length of the list -/

/-- The recursion for the length of the list. -/
theorem length_nineStrs_succ (n lo hi : ℕ) :
    (nineStrs (n + 1) lo hi).length = 9 * (nineStrs n lo hi).length
      + if hi = 0 then 0 else (nineStrs n (lo - 1) (hi - 1)).length := by
  rw [nineStrs, List.length_append, List.length_flatMap]
  congr 1
  · simp only [List.length_map, List.map_const', List.length_range, List.sum_replicate_nat]
  grind

/-- Strings without a nine: one more digit, nine times as many. -/
theorem nineTerm_zero (n : ℕ) :
    (n + 1).choose 0 * 9 ^ (n + 1 - 0) = 9 * (n.choose 0 * 9 ^ (n - 0)) := by
  grind

/-- Strings with g + 1 nines: the first digit is a nine or one of the nine other digits. -/
theorem nineTerm_succ (n g : ℕ) :
    (n + 1).choose (g + 1) * 9 ^ (n + 1 - (g + 1))
      = n.choose g * 9 ^ (n - g) + 9 * (n.choose (g + 1) * 9 ^ (n - (g + 1))) := by
  rw [Nat.choose_succ_succ, Nat.add_sub_add_right]
  rcases n.lt_or_ge (g + 1) with h | h
  · grind
  · rw [show n - g = n - (g + 1) + 1 by omega]
    ring

/-- A sum from 0: the first summand apart. -/
theorem sum_Icc_zero_succ (h : ℕ) (G : ℕ → ℕ) :
    ∑ f ∈ Finset.Icc 0 (h + 1), G f = G 0 + ∑ g ∈ Finset.Icc 0 h, G (g + 1) := by
  rw [← Nat.range_succ_eq_Icc_zero, ← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ', add_comm]

/-- A sum with both ends shifted by one. -/
theorem sum_Icc_succ_succ (l h : ℕ) (G : ℕ → ℕ) :
    ∑ f ∈ Finset.Icc (l + 1) (h + 1), G f = ∑ g ∈ Finset.Icc l h, G (g + 1) := by
  rw [← Finset.map_add_right_Icc, Finset.sum_map]
  rfl

/-- There are binom(n, f) 9^{n-f} strings with exactly f nines. -/
theorem length_nineStrs (n lo hi : ℕ) :
    (nineStrs n lo hi).length = ∑ f ∈ Finset.Icc lo hi, n.choose f * 9 ^ (n - f) := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs with h
    · subst h
      rw [Finset.sum_eq_single_of_mem 0 (by simp) fun b _ hb => by
        grind]
      rfl
    grind [Finset.sum_eq_zero]
  | succ n ih =>
    rw [length_nineStrs_succ, ih]
    rcases hi with _ | h
    · -- no nine is allowed
      rw [if_pos rfl, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl fun f hf => ?_
      grind
    · rw [if_neg (Nat.succ_ne_zero h), ih, Nat.add_sub_cancel]
      rcases lo with _ | l
      · rw [sum_Icc_zero_succ, sum_Icc_zero_succ, nineTerm_zero, mul_add,
          Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib]
        refine congrArg _ (Finset.sum_congr rfl fun g _ => ?_)
        rw [nineTerm_succ, add_comm]
      · rw [sum_Icc_succ_succ, sum_Icc_succ_succ, Nat.add_sub_cancel, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        grind [Finset.sum_congr, nineTerm_succ, add_comm]

/-! ## The first string -/

/-- If there is a string at all, the bounds are consistent. -/
theorem le_of_mem_nineStrs {n lo hi : ℕ} (hl : l ∈ nineStrs n lo hi) :
    lo ≤ n ∧ lo ≤ hi := by
  grind [mem_nineStrs]

/-- The least string begins with 0 if not all digits have to be nines. -/
theorem nineFirst_succ {n lo : ℕ} (h : lo ≤ n) :
    nineFirst (n + 1) lo = 0 :: nineFirst n lo := by
  grind [nineFirst, Nat.succ_sub]

/-- The string of nines. -/
theorem nineFirst_self_succ (n : ℕ) : nineFirst (n + 1) (n + 1) = 9 :: nineFirst n n := by
  grind [nineFirst]

/-- Without strings of n digits there are no strings of n + 1 digits that begin below 9. -/
theorem flatMap_map_nil (l : List ℕ) :
    l.flatMap (fun d => ([] : List (List ℕ)).map (d :: ·)) = [] :=
  by simp

theorem head?_nineStrs {n lo hi : ℕ} (h : lo ≤ n) (h' : lo ≤ hi := by omega) :
    (nineStrs n lo hi).head? = some (nineFirst n lo) := by
  induction n generalizing lo hi with
  | zero =>
    aesop
  | succ n ih =>
    rw [nineStrs]
    rcases n.lt_or_ge lo with hlo | hlo
    · -- all digits are nines
      obtain rfl : lo = n + 1 := by omega
      rw [nineStrs_eq_nil, if_neg (by omega), flatMap_map_nil,
        List.nil_append, List.head?_map, Nat.add_sub_cancel, ih le_rfl (by omega),
        nineFirst_self_succ]
      rfl
    grind [List.range_succ_eq_map, List.append_assoc, List.head?_append, List.head?_map, nineFirst_succ]

/-! ## From each string to the next -/

/-- f takes each member of the list to the following one, and the last one to z. -/
def NextTo {α : Type} (f : α → Option α) : List α → Option α → Prop
  | [], _ => True
  | x :: r, z => f x = r.head?.or z ∧ NextTo f r z

variable {α : Type} {f : α → Option α} {A : List α} {z : Option α}

/-- f goes through two lists one after the other exactly if it goes through both, and from the last
member of the first list to the first member of the second (to z if the second list is empty). -/
theorem nextTo_append {B : List α} :
    NextTo f (A ++ B) z ↔ NextTo f A (B.head?.or z) ∧ NextTo f B z := by
  induction A with
  | nil => tauto
  | cons x A ih =>
    grind [NextTo]

/-- What `NextTo` says about the member number i. -/
theorem NextTo.getElem     (h : NextTo f A z) (i : ℕ) (hi : i < A.length) : f A[i] = A[i + 1]?.or z := by
  induction A generalizing i with
  | nil => grind
  | cons x A ih =>
    cases i with
    | zero => rw [List.getElem_cons_zero, h.1, List.getElem?_cons_succ, List.head?_eq_getElem?]
    | succ i =>
      exact ih h.2 i (by simp_all)

/-- The block of the strings with the first digit d. -/
theorem nextTo_map_cons (lo hi n d : ℕ) (S : List (List ℕ)) (hS : ∀ l ∈ S, l.length = n)
    (h : NextTo (nineNext (if d = 9 then lo - 1 else lo) (if d = 9 then hi - 1 else hi)) S none) :
    NextTo (nineNext lo hi) (S.map (d :: ·)) (nineRaise lo hi n d) := by
  induction S with
  | nil => trivial
  | cons x r ih =>
    refine ⟨?_, ih (by simp_all) h.2⟩
    rw [nineNext, h.1]
    aesop

/-- The blocks of the strings with the first digits a, a + 1, …, a + k - 1, followed by the block
with the first digit 9: the end of the list `nineStrs (n + 1) lo hi`. -/
def nineBlocks (n lo hi a k : ℕ) : List (List ℕ) :=
  (List.range' a k).flatMap (fun d => (nineStrs n lo hi).map (d :: ·)) ++
    (if hi = 0 then [] else (nineStrs n (lo - 1) (hi - 1)).map (9 :: ·))

section

variable {n lo hi : ℕ}

/-- `nineNext` goes through the last block, the strings with the first digit 9. -/
theorem nextTo_nineBlocks_zero (a : ℕ)
    (h9 : NextTo (nineNext (lo - 1) (hi - 1)) (nineStrs n (lo - 1) (hi - 1)) none) :
    NextTo (nineNext lo hi) (nineBlocks n lo hi a 0) none := by
  rw [nineBlocks, List.range'_zero, List.flatMap_nil]
  split_ifs
  · trivial
  · exact nextTo_map_cons lo hi n 9 _ (fun _ => length_of_mem_nineStrs) h9

/-- The first string after the block with the first digit a is the one to which `nineNext` goes by
raising the digit a. -/
theorem head_nineBlocks (hn : lo ≤ n) (hh : lo ≤ hi) {a k : ℕ} (hak : a + 1 + k = 9) :
    (nineBlocks n lo hi (a + 1) k).head? = nineRaise lo hi n a := by
  rw [nineBlocks, nineRaise]
  cases k with
  | zero =>
    obtain rfl : a = 8 := by omega
    rw [List.range'_zero, List.flatMap_nil, List.nil_append]
    by_cases h0 : hi = 0
    · simp_all
    · rw [if_neg h0, List.head?_map, head?_nineStrs (by omega), if_neg (lt_irrefl 8),
        if_pos ⟨rfl, Nat.pos_of_ne_zero h0⟩]
      rfl
  | succ k =>
    rw [List.range'_succ, List.flatMap_cons, List.append_assoc, List.head?_append, List.head?_map,
      head?_nineStrs hn hh, if_pos (show a < 8 by omega)]
    rfl

/-- `nineNext` goes through the blocks. -/
theorem nextTo_nineBlocks (hn : lo ≤ n) (hh : lo ≤ hi)
    (h : NextTo (nineNext lo hi) (nineStrs n lo hi) none)
    (h9 : NextTo (nineNext (lo - 1) (hi - 1)) (nineStrs n (lo - 1) (hi - 1)) none) (k a : ℕ)
    (hak : a + k = 9) : NextTo (nineNext lo hi) (nineBlocks n lo hi a k) none := by
  induction k generalizing a with
  | zero => exact nextTo_nineBlocks_zero a h9
  | succ k ih =>
    have hsplit : nineBlocks n lo hi a (k + 1)
        = (nineStrs n lo hi).map (a :: ·) ++ nineBlocks n lo hi (a + 1) k := by
      grind [nineBlocks, List.range'_succ, List.append_assoc]
    grind [nextTo_append, head_nineBlocks, nextTo_map_cons, length_of_mem_nineStrs]

end

/-- `nineNext` goes through the list. -/
theorem nextTo_nineStrs (n lo hi : ℕ) :
    NextTo (nineNext lo hi) (nineStrs n lo hi) none := by
  induction n generalizing lo hi with
  | zero =>
    rw [nineStrs]
    split_ifs
    · tauto
    tauto
  | succ n ih =>
    by_cases h : lo ≤ n ∧ lo ≤ hi
    · exact nextTo_nineBlocks h.1 h.2 (by simp_all) (by simp_all) 9 0 rfl
    · -- only strings that begin with a nine
      rw [nineStrs, nineStrs_eq_nil]
      exact nextTo_nineBlocks_zero 0 (by simp_all)

/-- `nineNext` goes from each string of the list to the following one, and from the last one to
none. -/
theorem nineNext_getElem (n lo hi i : ℕ) (h : i < (nineStrs n lo hi).length) :
    nineNext lo hi ((nineStrs n lo hi)[i]) = (nineStrs n lo hi)[i + 1]? := by
  rw [(nextTo_nineStrs n lo hi).getElem, Option.or_none]

section

variable {n lo hi i : ℕ}

theorem nineStr_succ (n lo hi i : ℕ) :
    nineStr n lo hi (i + 1) = (nineNext lo hi (nineStr n lo hi i)).getD (nineStr n lo hi i) :=
  Function.iterate_succ_apply' _ _ _

/-- `nineStr n lo hi i` is the member number i of the list. -/
theorem getElem_nineStrs (h : i < (nineStrs n lo hi).length) :
    (nineStrs n lo hi)[i] = nineStr n lo hi i := by
  induction i with
  | zero =>
    obtain ⟨hn, hh⟩ := le_of_mem_nineStrs (List.getElem_mem h)
    apply Option.some.inj
    rw [← List.getElem?_eq_getElem, ← List.head?_eq_getElem?, head?_nineStrs hn hh]
    rfl
  | succ i ih =>
    grind [nineStr_succ, Nat.lt_of_succ_lt, nineNext_getElem, List.getElem?_eq_getElem]

theorem nineStr_mem (h : i < (nineStrs n lo hi).length) : nineStr n lo hi i ∈ nineStrs n lo hi :=
  getElem_nineStrs h ▸ List.getElem_mem h

/-- There is a next string exactly if the string is not the last one of the list. -/
theorem isSome_nineNext_nineStr (h : i < (nineStrs n lo hi).length) :
    (nineNext lo hi (nineStr n lo hi i)).isSome = decide (i + 1 < (nineStrs n lo hi).length) := by
  rw [← getElem_nineStrs h, nineNext_getElem]
  grind

/-- If the bounds are consistent, there is a string. -/
theorem length_nineStrs_pos (hn : lo ≤ n) (hh : lo ≤ hi) : 0 < (nineStrs n lo hi).length :=
  by grind [List.length_pos_iff, head?_nineStrs]
