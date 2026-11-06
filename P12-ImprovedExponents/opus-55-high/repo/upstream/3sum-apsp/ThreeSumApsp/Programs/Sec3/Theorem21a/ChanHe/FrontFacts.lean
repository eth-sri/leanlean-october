/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts
import ThreeSumApsp.Sec3.Theorem21a.ChanHe.FromNumbers
import ThreeSumApsp.Spec.Sec3.Problems

/-!
# 3SUM from Convolution-3SUM: what the lists that the first routines produce stand for

Theorem 21(a), after [CH20, Theorem 5.1].  The routines that run before the
recursion trees produce lists: the table of binary digits (`bitTable`), the selections by digits
(`pickList`), the distinct values with their multiplicities, and the doubles of the repeated values
(`twiceList`). This file has no program.  It shows that these lists represent the sets from which
the reduction makes its three-set inputs.

* A selection by one digit is `ChanHe.splitA`, a selection by two digits is `ChanHe.splitB`
  (`pick_splitA`, `pick_splitB`).
* `Values n X D C` says that `D` lists the distinct values of the input `X` and `C` how often each
  occurs.  Then `twiceList D C` represents `ChanHe.twiceSet` (`Values.twice`), and the test of
  zeroThree decides whether 0 occurs at least three times (`Values.zeroThree`).
-/


namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

/-! ## The table of binary digits -/

/-- A binary digit of the label of a number, as an integer. -/
def bitOf (V β : ℕ) (x : ℤ) : ℤ := if (lab V x).testBit β then 1 else 0

/-- The `Λ` lowest binary digits of `z`. -/
def bitRow (Λ z : ℕ) : List ℤ := (List.range Λ).map fun β => if z.testBit β then 1 else 0

@[simp] theorem length_bitRow (Λ z : ℕ) : (bitRow Λ z).length = Λ := by simp [bitRow]

/-- The table begins with the digits of the first label. -/
theorem bitTable_cons (V Λ : ℕ) (x : ℤ) (L : List ℤ) :
    bitTable V Λ (x :: L) = bitRow Λ (lab V x) ++ bitTable V Λ L := by
  rfl

/-- The table ends with the digits of the last label. -/
theorem bitTable_append (V Λ : ℕ) (L : List ℤ) (x : ℤ) :
    bitTable V Λ (L ++ [x]) = bitTable V Λ L ++ bitRow Λ (lab V x) := by
  simp [bitTable, bitRow]

/-- The table has `Λ` cells for each number. -/
theorem length_bitTable (V Λ : ℕ) (L : List ℤ) : (bitTable V Λ L).length = L.length * Λ := by
  induction L with
  | nil => aesop
  | cons x L ih =>
    grind [bitTable_cons, List.length_append, length_bitRow, List.length_cons, Nat.succ_mul, Nat.add_comm]

variable {β : ℕ}

/-- Cell `i Λ + β` of the table holds digit `β` of the label of the `i`-th number. -/
theorem getD_bitTable (V Λ : ℕ) (L : List ℤ) {i : ℕ} (hi : i < L.length) (hβ : β < Λ) :
    (bitTable V Λ L).getD (i * Λ + β) 0 = bitOf V β (L.getD i 0) := by
  induction L generalizing i with
  | nil => simp_all
  | cons x L ih =>
    rw [bitTable_cons]
    cases i with
    | zero =>
      grind [bitRow, bitOf]
    | succ i =>
      grind [List.getD_append_right, length_bitRow, Nat.succ_mul, List.getD_cons_succ]

/-! ## Selecting by binary digits -/

/-- A filter written with positions. -/
theorem filter_by_position (L : List ℤ) (q : ℤ → Bool) :
    ((List.range L.length).filter fun i => q (L.getD i 0)).map (fun i => L.getD i 0) =
      L.filter q := by
  have hL : L = (List.range L.length).map fun i => L.getD i 0 := by
    refine List.ext_getElem (by simp) fun i h1 h2 => ?_
    simp_all
  conv_rhs => rw [hL, List.filter_map]
  rfl

variable {β' : ℕ}

/-- The selection by cells of the table of digits is a filter of the list. -/
theorem pickList_eq (V Λ : ℕ) (hβ : β < Λ) (hβ' : β' < Λ) (b b' two : ℤ) (L : List ℤ) :
    pickList Λ β β' b b' two L (bitTable V Λ L) =
      L.filter fun x => decide (bitOf V β x = b ∧ (two = 0 ∨ bitOf V β' x = b')) := by
  grind [filter_by_position, pickList, List.filter_congr, getD_bitTable]

/-- The digit as an integer, against the digit as a Boolean. -/
theorem bitOf_eq_iff (V β : ℕ) (x : ℤ) (v : Bool) :
    bitOf V β x = (if v then 1 else 0) ↔ (lab V x).testBit β = v := by
  unfold bitOf
  grind

variable {L : List ℤ}

/-- The selection by one digit gives the set `splitA`. -/
theorem pick_splitA (V Λ : ℕ) (hβ : β < Λ) (hβ' : β' < Λ) (v : Bool) (b' : ℤ)
    (hL : L.Nodup) :
    (pickList Λ β β' (if v then 1 else 0) b' 0 L (bitTable V Λ L)).Nodup ∧
      (pickList Λ β β' (if v then 1 else 0) b' 0 L (bitTable V Λ L)).toFinset =
        splitA V β v L.toFinset := by
  rw [pickList_eq V Λ hβ hβ']
  refine ⟨hL.filter _, ?_⟩
  simp [splitA, bitOf_eq_iff]

/-- The selection by two digits gives the set `splitB`. -/
theorem pick_splitB (V Λ : ℕ) (hβ : β < Λ) (hβ' : β' < Λ) (v w : Bool)
    (hL : L.Nodup) :
    (pickList Λ β β' (if !v then 1 else 0) (if w then 1 else 0) 1 L (bitTable V Λ L)).Nodup ∧
      (pickList Λ β β' (if !v then 1 else 0) (if w then 1 else 0) 1 L (bitTable V Λ L)).toFinset =
        splitB V β β' v w L.toFinset := by
  rw [pickList_eq V Λ hβ hβ']
  refine ⟨hL.filter _, ?_⟩
  simp only [bitOf_eq_iff, splitB]
  simp

/-- A selection is not longer than the list. -/
theorem length_pickList_le (Λ β β' : ℕ) (b b' two : ℤ) (L BT : List ℤ) :
    (pickList Λ β β' b b' two L BT).length ≤ L.length := by
  unfold pickList
  grind

variable {n : ℕ} {X : List ℤ}

/-! ## The values of the input and how often they occur -/

/-- A list of `n` numbers is the list of the values of its vector. -/
theorem eq_ofFn_vecOf (hX : X.length = n) : X = List.ofFn (vecOf n X) := by
  refine List.ext_getElem (by simp_all) fun i h1 h2 => ?_
  grind [vecOf]

/-- The set of the members of a list of `n` numbers is the image of its vector. -/
theorem toFinset_eq_image (hX : X.length = n) :
    X.toFinset = univ.image (vecOf n X) := by
  conv_lhs => rw [eq_ofFn_vecOf hX]
  aesop

/-- How often a value occurs in a list of `n` numbers, in terms of its vector. -/
theorem count_eq_card (hX : X.length = n) (a : ℤ) :
    X.count a = #{i : Fin n | vecOf n X i = a} := by
  conv_lhs => rw [eq_ofFn_vecOf hX]
  exact List.count_ofFn _ a

/-- `D` lists the distinct values of the input `X`, and `C` how often each occurs. -/
structure Values (n : ℕ) (X D C : List ℤ) : Prop where
  /-- No value stands twice. -/
  nodup : D.Nodup
  /-- The members of `D` are the values of the input. -/
  values : D.toFinset = univ.image (vecOf n X)
  /-- `C` says at how many positions each value stands. -/
  counts : C = D.map fun a => ((#{i : Fin n | vecOf n X i = a} : ℕ) : ℤ)

variable {D : List ℤ}

/-- The distinct values of a rearrangement of the input, with how often each occurs there. -/
theorem Values.of_perm {Ls : List ℤ} (hX : X.length = n) (hp : Ls.Perm X)
    (hD : D.Nodup) (hv : D.toFinset = Ls.toFinset) :
    Values n X D (D.map fun a => (Ls.count a : ℤ)) :=
  ⟨hD, by rw [hv, List.toFinset_eq_of_perm _ _ hp, toFinset_eq_image hX],
    by grind [List.map_congr_left, count_eq_card]⟩

variable {C : List ℤ}

/-- There are at most `n` distinct values. -/
theorem Values.length_le (h : Values n X D C) : D.length ≤ n := by
  rw [← List.toFinset_card_of_nodup h.nodup, h.values]
  exact card_image_univ_le _

/-- The pairs of a value and the number of its occurrences. -/
theorem Values.zip (h : Values n X D C) :
    D.zip C = D.map fun a => (a, ((#{i : Fin n | vecOf n X i = a} : ℕ) : ℤ)) := by
  rw [h.counts]
  exact List.map_prod_left_eq_zip.symm

/-- The doubles of the repeated values. -/
theorem Values.twice (h : Values n X D C) :
    (twiceList D C).Nodup ∧ (twiceList D C).toFinset = twiceSet (vecOf n X) := by
  have hfilter : twiceList D C =
      (D.filter fun a => decide (a ≠ 0 ∧ 2 ≤ #{i : Fin n | vecOf n X i = a})).map
        fun a => 2 * a := by
    unfold twiceList
    rw [h.zip, List.filter_map, List.map_map]
    simp_all [List.filter_congr]
  rw [hfilter]
  refine ⟨(h.nodup.filter _).map fun a b hab => by omega, ?_⟩
  have hmem : ∀ a : ℤ, a ∈ D ↔ a ∈ univ.image _ := fun a => by
    rw [← h.values, List.mem_toFinset]
  ext y
  simp_all [twiceSet]

/-- There are at most as many doubles as values. -/
theorem length_twiceList_le (D C : List ℤ) : (twiceList D C).length ≤ D.length := by
  unfold twiceList
  grind

/-- Whether 0 occurs at least three times. -/
theorem Values.zeroThree (h : Values n X D C) :
    (∃ q ∈ D.zip C, q.1 = 0 ∧ 3 ≤ q.2) ↔ 3 ≤ #{i : Fin n | vecOf n X i = 0} := by
  rw [h.zip]
  constructor
  · simp
  · intro h3
    have hne : #{i : Fin n | vecOf n X i = 0} ≠ 0 := by omega
    have h0 : 0 ∈ D := by
      rw [← List.mem_toFinset, h.values]
      simp_all
    simp_all
