/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Sec4.BoxesFromLeaves
import ThreeSumApsp.Sec4.Theorem30
import ThreeSumApsp.Spec.Sec4.Theorem30.Cubes
import ThreeSumApsp.Spec.Sec4.Theorem30.NineStrings

/-!
# What a query reads (proof of Theorem 30, "Query")

The output string, which the paper calls w, is η as a string of variables and w as the list of its
digits; the levels of its inner set Q are the positions of the digit 9.  w is also the list of
digits of the private leaf of η, and `scatter w s` replaces its m nines by a string s of m digits:
the paper's "forming its leaf or its box from the private leaf".  A query adds up the products at
the leaves of order below t contributing to η, and the stored values of the boxes of η (steps (2)
and (3) of the query in Section 4.3).

* `lowList`: the strings with at least m - t + 1 nines give the leaves of order below t ("Each of
  these leaves is obtained from the private leaf of w, which has P₀ at every level of Q, by picking
  fewer than t of those levels and replacing P₀ with one of the nine other terms at each of them");
* `boxesOf`: the strings with exactly m - t nines give the leaves of order exactly t, and `starRun`
  turns the leading nines into stars.  This is the second description of the boxes of w in
  Section 4.2: "For such a leaf, consider the lowest level of Q at which it chooses a term other
  than P₀, and replace its P₀ by a star at every lower level of Q (or at every level of Q, if
  t = 0).  The result is a box of w, and each box of w arises exactly once in this way".  On cubes
  the result is `starBelow`, and the members of the list are exactly the strings of the cubes
  `starBelow η τ` for these leaves τ (`mem_boxesOf_iff`; no other proof rests on this statement).
  In the first description the nines are the levels of V, and the leading nines those of F_V, which
  "is the longest initial segment of Q contained in V".  `starRunIf` is `starRun` as a pass over the
  string with one flag.

The results are `sum_lowList` and `sum_boxesOf` (a sum over one of the lists is the sum over the set
of the paper) and `sum_queryTerms_storedD` (the numbers that a query adds up have the sum of the
query of the paper). Each list is compared with its set by counting
(`List.sum_map_eq_sum_of_length_eq_card`):
1. The list has no repetitions: `scatter w` is injective on strings of m digits, and `starRun` can
   be undone (`lowList_nodup`, `boxesOf_nodup`).
2. Each member is the list of digits of a member of the set.  `scatter w s` is a leaf τ contributing
   to η with as many symbols P₀ as s has nines (`exists_leaf_scatter`).  With at least m - t + 1
   nines its order is below t (`exists_of_mem_lowList`).  With exactly m - t nines its order is t.
   The cube `starBelow η τ` has the digits of τ with stars at the levels of F_Z, where Z, the set
   of the levels of Q at which τ chooses P₀, is the nines of s.  `Unreached` is the formula for F_Z
   read on digits (`unreached_iff_mem_FV`); it holds exactly at the leading nines of s
   (`getD_scatter_starRun`), so the cube has the digits `scatter w (starRun s)`
   (`digitsC_starBelow`, `exists_leaf_of_mem_boxesOf`), and it is a box of η (`starBelow_mem`,
   `exists_of_mem_boxesOf`).
3. The lists have ∑_{d<t} α_d and α_t members (`length_lowList`, `length_boxesOf`), and so have the
   sets, by the last line of Lemma 28 (`lemma_28_counts`).
-/


namespace ThreeSumApsp.Spec

/-- The list w with its digits 9 replaced, from the left, by the digits of s. -/
def scatter : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | x :: w, [] => x :: w
  | x :: w, d :: s => if x = 9 then d :: scatter w s else x :: scatter w (d :: s)

/-- The leaves of order below t contributing to the output string with the digits w, in
lexicographic order: at the m levels of Q they have at least m - t + 1 digits 9. -/
def lowList (m t : ℕ) (w : List ℕ) : List (List ℕ) := (nineStrs m (m - t + 1) m).map (scatter w)

/-- The leading digits 9 turned into 10: F_V "is the longest initial segment of Q contained in V"
(Section 4.2). -/
def starRun : List ℕ → List ℕ
  | [] => []
  | d :: l => if d = 9 then 10 :: starRun l else d :: l

/-- The boxes of the output string with the digits w.  "There is another way to describe the boxes
of w, in terms of the leaves of order exactly t contributing to w.  For such a leaf, consider the
lowest level of Q at which it chooses a term other than P₀, and replace its P₀ by a star at every
lower level of Q (or at every level of Q, if t = 0)" (Section 4.2).  Such a leaf has at the m levels
of Q a string with exactly m - t digits 9, and the leading ones are turned into stars
(`mem_boxesOf_iff`). -/
def boxesOf (m t : ℕ) (w : List ℕ) : List (List ℕ) :=
  (nineStrs m (m - t) (m - t)).map fun s => scatter w (starRun s)

/-- The numbers that a query adds up, in the order in which it adds them: the products at the leaves
of `lowList`, read from the two encodings, then the stored values of the boxes of `boxesOf`;
`stored l` is the value stored for the box l. -/
def queryTerms (m t : ℕ) (encA encB : List ℤ) (stored : List ℕ → ℤ) (w : List ℕ) : List ℤ :=
  (lowList m t w).map (leafProduct encA encB) ++ (boxesOf m t w).map stored

variable (w : List ℕ)

/-! ## Putting a string at the positions of the nines -/

theorem scatter_nil_right : scatter w [] = w := by
  cases w <;> rfl

/-- A digit other than 9 is kept. -/
theorem scatter_cons_of_ne {x : ℕ} (hx : x ≠ 9) (w s : List ℕ) :
    scatter (x :: w) s = x :: scatter w s := by
  cases s with
  | nil => grind [scatter_nil_right]
  | cons d s => grind [scatter]

/-- A digit 9 is replaced by the next digit of the string. -/
theorem scatter_nine_cons (d : ℕ) (s : List ℕ) :
    scatter (9 :: w) (d :: s) = d :: scatter w s := by
  rfl

/-- The string has the length of w. -/
theorem length_scatter (s : List ℕ) : (scatter w s).length = w.length := by
  fun_induction scatter w s <;> simp_all

variable {s : List ℕ} {d : ℕ}

/-- Every digit of `scatter w s` is a digit of w or of s. -/
theorem mem_of_mem_scatter {w : List ℕ} (h : d ∈ scatter w s) :
    d ∈ w ∨ d ∈ s := by
  fun_induction scatter w s <;> grind

/-- At a position where w has no 9, its digit is kept. -/
theorem getD_scatter_of_ne (s : List ℕ) (i : ℕ) (h : w.getD i 0 ≠ 9) :
    (scatter w s).getD i 0 = w.getD i 0 := by
  fun_induction scatter w s generalizing i <;> cases i <;> simp_all

/-- `scatter w s` has as many nines as s. -/
theorem count_nine_scatter (s : List ℕ) (hs : s.length = w.count 9) :
    (scatter w s).count 9 = s.count 9 := by
  fun_induction scatter w s <;> grind

/-- Strings of the right length are determined by what `scatter w` makes of them. -/
theorem scatter_inj (s s' : List ℕ) (hs : s.length = w.count 9)
    (hs' : s'.length = w.count 9) (h : scatter w s = scatter w s') : s = s' := by
  fun_induction scatter w s generalizing s' <;> cases s' <;> grind [scatter]

/-! ## The leading nines turned into stars -/

theorem length_starRun (s : List ℕ) : (starRun s).length = s.length := by
  fun_induction starRun s <;> simp_all

/-- Turning the stars back into nines undoes `starRun`. -/
theorem starsToNines_starRun (h : 10 ∉ s) : starsToNines (starRun s) = s := by
  fun_induction starRun s with
  | case1 => rfl
  | case2 l ih => simp_all [starsToNines]
  | case3 d l hd => exact starsToNines_of_notMem h

/-- `starRun` continued on the rest of a string that is read digit by digit: flag says that all the
digits read so far were nines, so the run of stars goes on; otherwise the rest is kept. -/
def starRunIf (flag : Bool) (s : List ℕ) : List ℕ := if flag then starRun s else s

/-- A digit other than 9 ends the run. -/
theorem starRunIf_cons_of_ne (hd : d ≠ 9) (flag : Bool) (s : List ℕ) :
    starRunIf flag (d :: s) = d :: starRunIf false s := by
  grind [starRunIf, starRun]

/-- A digit 9 becomes a star while the run goes on, and the run goes on. -/
theorem starRunIf_nine_cons (flag : Bool) (s : List ℕ) :
    starRunIf flag (9 :: s) = (if flag then 10 else 9) :: starRunIf flag s := by
  aesop

/-- Position i is one of "the levels that we have not reached" (F_V, Section 4.2).  Here w is the
list of digits of the output string, so its nines are the levels of Q, and u is the list of digits
of a leaf, whose nines among them are the levels of V: i is a level of Q below every level of Q ∖ V.
-/
def Unreached (w u : List ℕ) (i : ℕ) : Prop :=
  w.getD i 0 = 9 ∧ ∀ j, w.getD j 0 = 9 → u.getD j 0 ≠ 9 → i < j

variable (x : ℕ)

/-- The first position is not reached if it is a level of V. -/
theorem unreached_cons_zero (y : ℕ) (w u : List ℕ) :
    Unreached (x :: w) (y :: u) 0 ↔ x = 9 ∧ y = 9 := by
  grind [Unreached]

/-- A later position is not reached if the first position is no level of Q ∖ V and the position is
not reached in the rest. -/
theorem unreached_cons_succ (y : ℕ) (w u : List ℕ) (i : ℕ) :
    Unreached (x :: w) (y :: u) (i + 1) ↔ (x = 9 → y = 9) ∧ Unreached w u i := by
  rw [Unreached, Unreached, ← Nat.and_forall_add_one]
  grind

/-- Turning the leading nines of s into stars puts stars at the positions given by the formula for
F_V, and changes nothing else. -/
theorem getD_scatter_starRun (s : List ℕ) (hs : s.length = w.count 9) (i : ℕ) :
    (Unreached w (scatter w s) i → (scatter w (starRun s)).getD i 0 = 10) ∧
      (¬ Unreached w (scatter w s) i →
        (scatter w (starRun s)).getD i 0 = (scatter w s).getD i 0) := by
  induction w generalizing s i with
  | nil => simp [scatter, Unreached]
  | cons x w ih =>
    by_cases hx : x = 9
    · subst hx
      rw [List.count_cons_self] at hs
      obtain ⟨d, s, rfl⟩ := List.exists_cons_of_length_eq_add_one hs
      by_cases hd : d = 9
      · subst hd
        rw [starRun, if_pos rfl, scatter_nine_cons, scatter_nine_cons]
        cases i with
        | zero => simp [unreached_cons_zero]
        | succ i => grind [unreached_cons_succ]
      · rw [starRun, if_neg hd]
        exact ⟨fun h => absurd (h.2 0 rfl hd) (Nat.not_lt_zero i), by omega⟩
    · rw [scatter_cons_of_ne hx, scatter_cons_of_ne hx]
      cases i with
      | zero => grind [unreached_cons_zero]
      | succ i => grind [unreached_cons_succ]

/-! ## The leaves of order below t -/

section

variable {L m t : ℕ} {η : OutStr L}

/-- The output string has m nines. -/
theorem count_nine_digitsO (hη : (innerSetO η).card = m) :
    (digitsO η).count 9 = m := by
  grind [card_innerSetO]

variable {s : List ℕ}

/-- A string of digits below 10, put at the levels of Q, gives a leaf contributing to η that
chooses P₀ as often as the string has a nine. -/
theorem exists_leaf_scatter (hlen : s.length = (digitsO η).count 9)
    (hdig : ∀ d ∈ s, d < 10) :
    ∃ τ : Leaf L, digitsT τ = scatter (digitsO η) s ∧ Leaf.Contributes τ η ∧
      (P0Levels τ).card = s.count 9 := by
  obtain ⟨τ, hτ⟩ := exists_digitsT _
    (by rw [length_scatter, length_digitsO])
    fun d hd => (mem_of_mem_scatter hd).elim (digitsO_lt η d) (hdig d)
  refine ⟨τ, hτ, fun ℓ => ?_, ?_⟩
  · rw [contributes_iff, ← getD_digitsO, ← getD_digitsT, hτ]
    grind [getD_scatter_of_ne]
  grind [card_P0Levels, count_nine_scatter]

/-- Every member of the list is the list of digits of a leaf of order below t contributing to η. -/
theorem exists_of_mem_lowList (hη : (innerSetO η).card = m) (l : List ℕ)
    (h : l ∈ lowList m t (digitsO η)) : ∃ τ ∈ lowLeaves m t η, digitsT τ = l := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  obtain ⟨hlen, hdig, hlo, -⟩ := (mem_nineStrs s).mp hs
  obtain ⟨τ, hτ, hcontr, hcard⟩ :=
    exists_leaf_scatter (hlen.trans (count_nine_digitsO hη).symm) hdig
  refine ⟨τ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontr, ?_⟩, hτ⟩
  -- the order is m minus the number of nines, of which there are at least m - t + 1 (hlo)
  grind [order]

theorem lowList_nodup (hη : (innerSetO η).card = m) : (lowList m t (digitsO η)).Nodup := by
  have hcount := count_nine_digitsO hη
  exact (nineStrs_nodup _ _ _).map_on fun s hs s' hs' h => scatter_inj _ s s'
    (by grind [length_of_mem_nineStrs]) (by grind [length_of_mem_nineStrs]) h

/-- There are ∑_{d < t} α_d such leaves. -/
theorem length_lowList (ht : t ≤ m) (w : List ℕ) :
    (lowList m t w).length = ∑ d ∈ Finset.range t, alpha m d := by
  rw [lowList, List.length_map, length_nineStrs]
  -- a string with f nines gives a leaf of order d = m - f: reflect the sum
  refine Finset.sum_nbij' (fun f => m - f) (fun d => m - d) ?_ ?_ ?_ ?_
    fun f hf => by simp_all [alpha]
  all_goals
    grind

/-- **The first sum of a query**: a sum over the list is the sum over the leaves of order below t
contributing to η. -/
theorem sum_lowList (ht : t ≤ m) (hη : (innerSetO η).card = m) (F : List ℕ → ℤ) :
    ((lowList m t (digitsO η)).map F).sum = ∑ τ ∈ lowLeaves m t η, F (digitsT τ) :=
  List.sum_map_eq_sum_of_length_eq_card _ (lowList_nodup hη) _ digitsT (digitsT_injective L)
    (exists_of_mem_lowList hη)
    (by grind [length_lowList, lemma_28_counts]) F

/-! ## The boxes -/

/-- The formula for F_V on digits is the formula of the paper, for V = Z. -/
theorem unreached_iff_mem_FV (τ : Leaf L) (ℓ : Fin L) :
    Unreached (digitsO η) (digitsT τ) ℓ ↔ ℓ ∈ FV (innerSetO η) (Zof (innerSetO η) τ) := by
  rw [Unreached, getD_digitsO_eq_nine, FV, Finset.mem_filter,
    forall_nine_digitsO]
  refine and_congr_right fun _ => ⟨fun h ℓ' hℓ' => ?_, fun h ℓ' hℓ' h9 => ?_⟩
  · obtain ⟨hQ, hZ⟩ := Finset.mem_sdiff.mp hℓ'
    refine h ℓ' hQ fun h9 => hZ (Finset.mem_filter.mpr ⟨hQ, ?_⟩)
    grind [getD_digitsT, termIdx_eq_nine]
  · refine h ℓ' (Finset.mem_sdiff.mpr ⟨hℓ', fun hZ => h9 ?_⟩)
    rw [getD_digitsT, termIdx_eq_nine]
    exact (Finset.mem_filter.mp hZ).2

/-- The cube of the second description of the boxes (Section 4.2): its digits are those of the leaf,
with the leading nines of the string at the levels of Q turned into stars. -/
theorem digitsC_starBelow {τ : Leaf L} (hs : s.length = (digitsO η).count 9)
    (hτ : digitsT τ = scatter (digitsO η) s) :
    digitsC (starBelow η τ) = scatter (digitsO η) (starRun s) := by
  refine digitsC_eq_of_getD _ (by rw [length_scatter, length_digitsO]) fun ℓ => ?_
  obtain ⟨hstar, hterm⟩ := getD_scatter_starRun _ s hs ℓ
  rw [← hτ, unreached_iff_mem_FV] at hstar hterm
  rw [starBelow, Cube.starAt]
  split_ifs with h
  · aesop
  grind [getD_digitsT, cubeIdx_term]

/-- Every member of the list arises, as in the second description of the boxes, from a leaf of order
exactly t contributing to η. -/
theorem exists_leaf_of_mem_boxesOf (ht : t ≤ m) (hη : (innerSetO η).card = m) (l : List ℕ)
    (h : l ∈ boxesOf m t (digitsO η)) :
    ∃ τ : Leaf L, (Leaf.Contributes τ η ∧ order m τ = t) ∧ digitsC (starBelow η τ) = l := by
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
  obtain ⟨hlen, hdig, hlo, hhi⟩ := (mem_nineStrs s).mp hs
  have hlen' : s.length = (digitsO η).count 9 := by simp_all [count_nine_digitsO]
  grind [exists_leaf_scatter, digitsC_starBelow, order]

/-- Every member of the list is the list of digits of a box of η: "The result is a box of w". -/
theorem exists_of_mem_boxesOf (ht : t ≤ m) (hη : (innerSetO η).card = m) (l : List ℕ)
    (h : l ∈ boxesOf m t (digitsO η)) : ∃ π ∈ (Vsets m t η).biUnion (BV η), digitsC π = l := by
  grind [exists_leaf_of_mem_boxesOf, starBelow_mem]

theorem boxesOf_nodup (hη : (innerSetO η).card = m) : (boxesOf m t (digitsO η)).Nodup := by
  have hcount := count_nine_digitsO hη
  refine (nineStrs_nodup _ _ _).map_on fun s hs s' hs' h => ?_
  grind [scatter_inj, length_starRun, length_of_mem_nineStrs, starsToNines_starRun, ten_notMem_of_mem_nineStrs]

/-- "This means that w has exactly α_t boxes." -/
theorem length_boxesOf (ht : t ≤ m) (w : List ℕ) : (boxesOf m t w).length = alpha m t := by
  grind [boxesOf, List.length_map, length_nineStrs, Finset.Icc_self, Finset.sum_singleton, alpha, Nat.choose_symm, Nat.sub_sub_self]

/-- **The second sum of a query**: a sum over the list is the sum over the boxes of η. -/
theorem sum_boxesOf (ht : t ≤ m) (hη : (innerSetO η).card = m) (F : List ℕ → ℤ) :
    ((boxesOf m t (digitsO η)).map F).sum = ∑ π ∈ (Vsets m t η).biUnion (BV η), F (digitsC π) :=
  List.sum_map_eq_sum_of_length_eq_card _ (boxesOf_nodup hη) _ digitsC (digitsC_injective L)
    (exists_of_mem_boxesOf ht hη)
    (by simp_all [length_boxesOf, lemma_28_counts]) F

end

/-! ## The query -/

/-- With the values of the dynamic program for the boxes, the numbers that a query adds up have the
sum of the query of the proof of Theorem 30. -/
theorem sum_queryTerms_storedD {L m t : ℕ} (ht : t ≤ m) (encA encB : Leaf L → ℤ) {η : OutStr L}
    (hη : (innerSetO η).card = m) :
    (queryTerms m t (arrT encA) (arrT encB) (storedD (arrT encA) (arrT encB)) (digitsO η)).sum
      = queryValue m t encA encB η := by
  rw [queryTerms, List.sum_append, sum_lowList ht hη, sum_boxesOf ht hη,
    Finset.sum_biUnion (BV_pairwiseDisjoint η _)]
  refine congrArg₂ _ (Finset.sum_congr rfl fun τ _ => leafProduct_digitsT encA encB τ)
    (Finset.sum_congr rfl fun V hV => Finset.sum_congr rfl fun π hπ => ?_)
  rw [storedD, dpValueD_digitsC, card_starLevels]
