/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts
import ThreeSumApsp.Spec.Sec3.Theorem21a.Passes

/-!
# 3SUM from Convolution-3SUM: distinct values, doubles of repeated values, a triple zero

Theorem 21(a), after [CH20, Theorem 5.1].  The three-set inputs of the
reduction for n numbers are made from the set of the values, from the doubles of the values that are
not 0 and occur at least twice (`ChanHe.twiceSet`), and from the set that is {0} if 0 occurs at
least three times and empty if not (`ChanHe.zeroSet`).  Three passes prepare these sets.

* zeroThree passes over the values and their multiplicities and answers whether 0 occurs at least
  three times (`zeroThree_spec`).
* twice passes over the same two lists and writes the doubles of the values that are not 0 and occur
  at least twice (`twice_spec`, with `twiceRound_runs` for one round).
* distinct passes over the sorted input and writes these two lists: the distinct values, and how
  often each occurs (`distinct_spec`, with `distinctRound_runs` for one round).

Each section first says what the pass has written or found after the first i elements, and how one
more element changes it.  The invariant of the loop is this, and the proof of a round compares the
tests of the program with the cases of that step.  The body of each loop is a block: a goal
`s.Runs lim σ R` is a pair, which says that the block s, started in σ, stays within the limits, and
that R holds of the state after it.  A procedure returns what its local 0 holds at the end.
-/


open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## zeroThree -/

/-- The answer of zeroThree for the first i values: 1 if one of them is 0 and occurs at least three
times, and 0 if not. -/
noncomputable def tripleZeroUpTo (D C : List ℤ) (i : ℕ) : ℤ :=
  flag (∃ j < i, D.getD j 0 = 0 ∧ 3 ≤ C.getD j 0)

theorem tripleZeroUpTo_zero (D C : List ℤ) : tripleZeroUpTo D C 0 = 0 := flag_of_not (by simp)

/-- One more value. -/
theorem tripleZeroUpTo_succ (D C : List ℤ) (i : ℕ) :
    tripleZeroUpTo D C (i + 1) =
      if D.getD i 0 = 0 ∧ 2 < C.getD i 0 then 1 else tripleZeroUpTo D C i := by
  split_ifs with h
  · exact flag_of ⟨i, Nat.lt_succ_self i, h⟩
  · exact flag_congr

variable {C : List ℤ}

/-- At the end the answer is the one that the specification asks for. -/
theorem tripleZeroUpTo_length {D : List ℤ} (hlen : C.length = D.length) :
    tripleZeroUpTo D C D.length = flag (∃ q ∈ D.zip C, q.1 = 0 ∧ 3 ≤ q.2) := by
  refine flag_congr ⟨?_, ?_⟩
  · rintro ⟨j, hj, hp⟩
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by omega)] at hp
    exact ⟨(D[j], C[j]), by grind [List.mem_iff_getElem], hp⟩
  · rintro ⟨q, hq, hp⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
    have hj' : j < D.length := by grind
    aesop

namespace ZeroThree

/- The locals of zeroThree: the arguments nd, val and mul, the counter, and the answer so far. -/
slots Len Val Mul Idx Found

end ZeroThree

open ZeroThree in
/-- zeroThree(nd, val, mul): the nd values stand at val and their multiplicities at mul.  Returns 1
if the value 0 occurs at least three times, and 0 if not. -/
def zeroThreeBody : Stmt :=
  .set Idx (k 0) ;;
  .set Found (k 0) ;;
  .while (v Idx <' v Len) (
    .ite (M (v Val +' v Idx) =' k 0)
      (.ite (k 2 <' M (v Mul +' v Idx)) (.set Found (k 1)) .skip)
      .skip ;;
    .set Idx (v Idx +' k 1)) ;;
  .set Len (v Found)

/-- The invariant of the loop of zeroThree before round number i: the answer so far is the answer
for the first i values, and the memory has not changed. -/
def ZeroThreeInv (μ : ℕ → ℤ) (val mul : ℕ) (D C : List ℤ) (i : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [D.length, val, mul, i, tripleZeroUpTo D C i], μ⟩

variable {p : ℕ}

/-- **zeroThree** meets its specification. -/
theorem zeroThree_spec (hP : P[p]? = some zeroThreeBody) : ZeroThreeSpec lim P p := by
  intro d val mul D C μ hlen hD hC hval hmul hw hword
  apply Meets.of_body hP
  unfold tZeroThree zeroThreeBody
  -- Idx := 0 ; Found := 0
  light_set 0
  light_set 0
  -- while Idx < Len
  refine Ends.next _ (Ends.whileBlock (ZeroThreeInv μ val mul D C) D.length ?_ ?_ ?_
    (hT := le_rfl)) (by simp; omega)
  · simp [ZeroThreeInv, tripleZeroUpTo_zero]
  ·
    -- if mem[Val + Idx] = 0 then if 2 < mem[Mul + Idx] then Found := 1 ; Idx := Idx + 1
    rintro i _ hi rfl
    have hstep := tripleZeroUpTo_succ D C i
    rw [← hD.getD hi, ← hC.getD (by omega)] at hstep
    by_cases h0 : μ (val + i) = 0 <;> by_cases h2 : 2 < μ (mul + i) <;>
      simp [Stmt.Runs, ZeroThreeInv, update_frame_setLocal, hstep, h0, h2, Limits.Addr, abs_le] <;>
      omega
  ·
    -- Len := Found
    rintro _ rfl
    exact ⟨by light_side, by light_side, Ends.setTo (tripleZeroUpTo D C D.length)
      ⟨tripleZeroUpTo_length hlen, rfl⟩⟩

/-! ## twice -/

/-- What twice has written after it has seen the first i values. -/
def twicePart (D C : List ℤ) (i : ℕ) : List ℤ :=
  passList (fun q : ℤ × ℤ => decide (q.1 ≠ 0 ∧ 2 ≤ q.2)) (fun q => 2 * q.1) (D.zip C) i

/-- One more value: its double is written if it is not 0 and occurs at least twice. -/
theorem twicePart_succ {D : List ℤ} (hlen : C.length = D.length) {i : ℕ} (hi : i < D.length) :
    twicePart D C (i + 1) =
      if D.getD i 0 ≠ 0 ∧ 1 < C.getD i 0 then twicePart D C i ++ [2 * D.getD i 0]
      else twicePart D C i := by
  have hi' : i < (D.zip C).length := by simp_all
  split_ifs with h
  · exact (passList_succ_of _ hi' (by grind)).trans (by aesop)
  · exact passList_succ_of_not _ hi' (by simp_all)

/-- At the end all the doubles are written. -/
theorem twicePart_length {D : List ℤ} (hlen : C.length = D.length) :
    twicePart D C D.length = twiceList D C := by
  have hzip : (D.zip C).length = D.length := by simp_all
  rw [twicePart, ← hzip, passList_length]
  rfl

namespace Twice

/- The locals of twice: the arguments nd, val, mul and out, the counter, and the number of cells
written. -/
slots Len Val Mul Out Idx Written

end Twice

open Twice in
/-- One round of twice: the double of the next value is written if the value is not 0 and occurs at
least twice. -/
def twiceRound : Stmt :=
  .iteNe (M (v Val +' v Idx)) (k 0)
    (.ite (k 1 <' M (v Mul +' v Idx))
      (.store (v Out +' v Written) (k 2 *' M (v Val +' v Idx)) ;;
        .set Written (v Written +' k 1))
      .skip)
    .skip ;;
  .set Idx (v Idx +' k 1)

open Twice in
/-- twice(nd, val, mul, out): the nd values stand at val and their multiplicities at mul.  Writes
the doubles of the values that are not 0 and occur at least twice to out, and returns their number.
-/
def twiceBody : Stmt :=
  .set Idx (k 0) ;;
  .set Written (k 0) ;;
  .while (v Idx <' v Len) twiceRound ;;
  .set Len (v Written)

/-- The invariant of the loop of twice before round number i: the doubles for the first i values
stand at out, and no other cell has changed. -/
def TwiceInv (μ : ℕ → ℤ) (val mul out : ℕ) (D C : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ, σ = ⟨frame [D.length, val, mul, out, i, (twicePart D C i).length], μ'⟩ ∧
    Seg μ' out (twicePart D C i) ∧ SameOutside μ μ' out D.length

variable {σ : State}

/-- One round of twice keeps the invariant. -/
theorem twiceRound_runs {μ : ℕ → ℤ} {val mul out V i : ℕ} {D : List ℤ}
    (K : Twice.Ctx lim μ val mul out V D C) (hi : i < D.length)
    (hI : TwiceInv μ val mul out D C i σ) :
    twiceRound.Runs lim σ (TwiceInv μ val mul out D C (i + 1)) := by
  obtain ⟨μ', rfl, hseg, hsame⟩ := hI
  -- where the regions lie
  light_facts K
  have hle : (twicePart D C i).length ≤ i := length_passList_le _ _ _ _
  -- what the program reads
  have hreadVal : μ' (val + i) = D.getD i 0 := (hsame _ (by omega)).trans (by aesop)
  have hreadMul : μ' (mul + i) = C.getD i 0 :=
    (hsame _ (by omega)).trans (by aesop)
  have hfits := abs_le.1 (K.bounded.getElem hi)
  rw [← List.getD_eq_getElem _ 0] at hfits
  have hstep := twicePart_succ K.len hi
  rw [← hreadVal, ← hreadMul] at hstep
  by_cases h0 : μ' (val + i) = 0
  · -- the value is 0: Idx := Idx + 1
    exact ⟨by simp [twiceRound, h0, Limits.Addr, abs_le]; omega, μ',
      by simp_all [twiceRound, update_frame_setLocal], by simp_all, hsame⟩
  by_cases h1 : 1 < μ' (mul + i)
  · -- mem[Out + Written] := 2 * mem[Val + Idx] ; Written := Written + 1 ; Idx := Idx + 1
    rw [if_pos ⟨h0, h1⟩] at hstep
    exact ⟨by light_side [twiceRound, h0, h1],
      Function.update μ' _ _,
      by simp_all [twiceRound, update_frame_setLocal], hstep ▸ hseg.snoc _,
      hsame.write (by omega) _⟩
  · -- the value occurs once: Idx := Idx + 1
    rw [if_neg (by omega)] at hstep
    exact ⟨by simp [twiceRound, h1, Limits.Addr, abs_le]; omega, μ',
      by simp [twiceRound, update_frame_setLocal, h1, hstep], by simp_all, hsame⟩

/-- **twice** meets its specification. -/
theorem twice_spec (hP : P[p]? = some twiceBody) : TwiceSpec lim P p := by
  intro d val mul out V D C μ K
  light_facts K
  apply Meets.of_body hP
  unfold tTwice twiceBody
  -- Idx := 0 ; Written := 0
  light_set 0
  light_set 0
  -- while Idx < Len
  refine Ends.next _ (Ends.whileBlock (TwiceInv μ val mul out D C) D.length ?_ ?_ ?_
    (hT := le_rfl)) (by simp [twiceRound]; omega)
  · exact ⟨μ, by rfl, by tauto, .refl⟩
  ·
    intro i σ hi hI
    obtain ⟨μ', rfl, -⟩ := id hI
    exact ⟨by light_side, by light_side, twiceRound_runs K hi hI⟩
  ·
    -- Len := Written
    rintro _ ⟨μ', rfl, hseg, hsame⟩
    rw [twicePart_length K.len] at hseg
    exact ⟨by light_side, by light_side, Ends.setTo (twiceList D C).length
      ⟨rfl, hseg, hsame⟩ (by simp_all [twicePart_length]) (by simp [twiceRound]; omega)⟩

/-! ## distinct -/

/-- What distinct has written after it has seen the first i elements of the sorted list L: their
distinct values D stand at val, how often each has occurred stands at mul, and no other cell has
changed. -/
structure DistinctMem (μ μ' : ℕ → ℤ) (val mul : ℕ) (L D : List ℤ) (i : ℕ) : Prop where
  /-- D lists the distinct values among the first i elements. -/
  values : DistSt L D i
  /-- The values stand at val. -/
  segVal : Seg μ' val D
  /-- Their numbers of occurrences so far stand at mul. -/
  segMul : Seg μ' mul (D.map (countTo L i))
  /-- No other cell has changed. -/
  same : SameOutside2 μ μ' val L.length mul L.length

namespace DistinctMem

variable {μ μ' : ℕ → ℤ} {val mul i : ℕ} {L D : List ℤ}

/-- An element that differs from the last value opens a new cell of val and a new cell of mul. -/
theorem opens (h : DistinctMem μ μ' val mul L D i) (hs : L.Pairwise (· ≤ ·)) (hi : i < L.length)
    (hap : Apart val L.length mul L.length)
    (hne : D.length = 0 ∨ L.getD i 0 ≠ D.getD (D.length - 1) 0) :
    DistinctMem μ
      (Function.update (Function.update μ' (val + D.length) (L.getD i 0)) (mul + D.length) 1)
      val mul L (D ++ [L.getD i 0]) (i + 1) := by
  obtain ⟨hvalues, hnew⟩ := h.values.opens hs hi hne
  have hle := h.values.le
  refine ⟨hvalues, (h.segVal.snoc _).update_out (by grind) _, ?_,
    (h.same.write (by omega) _).write (by omega) _⟩
  rw [map_countTo_opens h.values hi hnew]
  simpa using (h.segMul.update_out (b := val + D.length) (by grind) _).snoc 1

/-- An element that equals the last value raises the last cell of mul by one. -/
theorem bumps (h : DistinctMem μ μ' val mul L D i) (hi : i < L.length)
    (hap : Apart val L.length mul L.length) (hpos : 0 < D.length)
    (he : L.getD i 0 = D.getD (D.length - 1) 0) :
    DistinctMem μ
      (Function.update μ' (mul + (D.length - 1)) (countTo L i (D.getD (D.length - 1) 0) + 1))
      val mul L D (i + 1) := by
  have hle := h.values.le
  refine ⟨h.values.bumps hi hpos he, h.segVal.update_out (by omega) _, ?_,
    h.same.write (by omega) _⟩
  rw [map_countTo_bumps h.values hi hpos he]
  exact h.segMul.update_in _

end DistinctMem

namespace Distinct

/- The locals of distinct: the arguments n, a, val and mul, the counter, and the number of distinct
values so far. -/
slots Len Src Val Mul Idx Values

end Distinct

open Distinct in
/-- A new value opens a new cell of val and of mul. -/
def distinctOpen : Stmt :=
  .store (v Val +' v Values) (M (v Src +' v Idx)) ;;
  .store (v Mul +' v Values) (k 1) ;;
  .set Values (v Values +' k 1)

open Distinct in
/-- One round of distinct: the next element opens a cell if there is no value yet or if it differs
from the last value, and raises the last cell of mul if not. -/
def distinctRound : Stmt :=
  .ite (v Values =' k 0) distinctOpen
    (.iteNe (M (v Src +' v Idx)) (M (v Val +' v Values -' k 1)) distinctOpen
      (.store (v Mul +' v Values -' k 1) (M (v Mul +' v Values -' k 1) +' k 1))) ;;
  .set Idx (v Idx +' k 1)

open Distinct in
/-- distinct(n, a, val, mul): a sorted list of n numbers stands at a.  Writes its distinct values to
val and how often each occurs to mul, and returns the number of distinct values. -/
def distinctBody : Stmt :=
  .set Idx (k 0) ;;
  .set Values (k 0) ;;
  .while (v Idx <' v Len) distinctRound ;;
  .set Len (v Values)

/-- The invariant of the loop of distinct before round number i: the memory is as `DistinctMem`
says for the first i elements, and Values holds the number of distinct values among them. -/
def DistinctInv (μ : ℕ → ℤ) (a val mul : ℕ) (L : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (D : List ℤ), σ = ⟨frame [L.length, a, val, mul, i, D.length], μ'⟩ ∧
    DistinctMem μ μ' val mul L D i

/-- One round of distinct keeps the invariant. -/
theorem distinctRound_runs {μ : ℕ → ℤ} {a val mul i : ℕ} {L : List ℤ}
    (C : Distinct.Ctx lim μ a val mul L) (hi : i < L.length)
    (hI : DistinctInv μ a val mul L i σ) :
    distinctRound.Runs lim σ (DistinctInv μ a val mul L (i + 1)) := by
  obtain ⟨μ', D, rfl, hmem⟩ := hI
  -- where the regions lie
  have hle := hmem.values.le
  light_facts C
  have hread : μ' (a + i) = L.getD i 0 :=
    (hmem.same _ ⟨by omega, by omega⟩).trans (by aesop)
  have hopen := hmem.opens C.sorted hi C.apart
  by_cases h0 : D.length = 0
  · -- no value yet: open a cell ; Idx := Idx + 1
    exact ⟨by light_side [distinctRound, distinctOpen, h0], _, _,
      by simp_all [distinctRound, distinctOpen, update_frame_setLocal], hopen (.inl h0)⟩
  have haddrVal : ((val : ℤ) + D.length - 1).toNat = val + (D.length - 1) := by omega
  have haddrMul : ((mul : ℤ) + D.length - 1).toNat = mul + (D.length - 1) := by omega
  have hlast : μ' _ = D.getD (D.length - 1) 0 := hmem.segVal.getD (by omega) 0
  by_cases he : μ' (a + i) = μ' (val + (D.length - 1))
  · -- the last value again: mem[Mul + Values - 1] := mem[Mul + Values - 1] + 1 ; Idx := Idx + 1
    have hcount : μ' (mul + (D.length - 1)) = countTo L i (D.getD (D.length - 1) 0) := by
      rw [hmem.segMul _ (by grind), List.getElem_map,
        List.getD_eq_getElem _]
    have := countTo_nonneg L i (D.getD (D.length - 1) 0)
    have := countTo_le L i (D.getD (D.length - 1) 0)
    exact ⟨by light_side [distinctRound, h0, he, haddrVal, haddrMul], _, _,
      by simp_all [distinctRound, update_frame_setLocal], hmem.bumps hi C.apart (by omega) (by omega)⟩
  · -- another value: open a cell ; Idx := Idx + 1
    exact ⟨by light_side [distinctRound, distinctOpen, h0, he, haddrVal],
      _, _, by simp_all [distinctRound, distinctOpen, update_frame_setLocal],
      hopen (by omega)⟩

/-- **distinct** meets its specification. -/
theorem distinct_spec (hP : P[p]? = some distinctBody) : DistinctSpec lim P p := by
  intro d a val mul L μ C
  light_facts C
  apply Meets.of_body hP
  unfold tDistinct distinctBody
  -- Idx := 0 ; Values := 0
  light_set 0
  light_set 0
  -- while Idx < Len
  refine Ends.next _ (Ends.whileBlock (DistinctInv μ a val mul L) L.length ?_ ?_ ?_
    (hT := le_rfl)) (by simp [distinctRound, distinctOpen]; omega)
  · exact ⟨μ, [], rfl, DistSt.zero L, Seg.nil, Seg.nil, .refl⟩
  ·
    intro i σ hi hI
    obtain ⟨μ', D, rfl, -⟩ := id hI
    exact ⟨by light_side, by light_side, distinctRound_runs C hi hI⟩
  ·
    -- Len := Values
    rintro _ ⟨μ', D, rfl, hmem⟩
    refine ⟨by light_side, by light_side, Ends.setTo D.length
      ⟨⟨D, rfl, hmem.values.nodup, ?_, hmem.segVal, ?_⟩, hmem.same⟩
      (hT := by simp [distinctRound, distinctOpen]; omega)⟩
    · ext x
      rw [List.mem_toFinset, List.mem_toFinset, hmem.values.mem, List.take_length]
    · have hcount : countTo L L.length = fun x => (L.count x : ℤ) := by
        grind [countTo]
      exact hcount ▸ hmem.segMul
