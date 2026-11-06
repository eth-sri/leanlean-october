/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts
public import Mathlib.Data.Bool.Count

/-!
# The digits of the output string of a position

Proof of Theorem 30, "Query": "Given (I, J), we find its tile from the bands of row I and column J,
the subset Q of its block product, and its output string w (whose variables at the levels outside Q
we read off the row and column of (I, J) within the block product), all in O(L) operations". The
routine walks the mask of the subset: it writes the digit 9 at a level of the subset (levelInner),
and otherwise 3 x + y for the next base-3 digits x and y of the offsets of I and J (levelOuter). The
invariant OutDigits.Inv says what has been written before level l; each of the two branches takes it
from l to l + 1 (OutDigits.inner, OutDigits.outer).
-/

@[expose] public section

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The program -/


/-- A level of the subset: wd[level] := 9; level := level + 1. -/
def levelInner  :=
  .store (v 7 +' v 9) (k 9) ;;
  .set 9 (v 9 +' k 1)

/-- A level outside the subset: wd[level] := 3 dI[outer] + dJ[outer]; outer := outer + 1;
level := level + 1. -/
def levelOuter  :=
  .store (v 7 +' v 9) (k 3 *' M (v 2 +' v 10) +' M (v 3 +' v 10)) ;;
  .set 10 (v 10 +' k 1) ;;
  .set 9 (v 9 +' k 1)

/-- The walk along the mask: while level < L, treat the level according to mask[level]. -/
def outDigitsWalk : Stmt :=
  .while (v 9 <' v 6) (.ite (M (v 8 +' v 9) =' k 1) levelInner levelOuter)

/-- outDigits(gI, gJ, dI, dJ, aMASK, K0, L, wd) writes the L digits of the output string at wd. -/
def outDigitsBody  :=
  .set 8 (v 4 +' (v 0 *' v 5 +' v 1) *' v 6) ;;
  .set 9 (k 0) ;;
  .set 10 (k 0) ;;
  outDigitsWalk

namespace OutDigits

/-! ## The pure side: the digit at one level -/

variable {lim : Limits} {μ : Light.Memory} {x : OutDigitsArgs} {l : ℕ} {σ : State}

/-- The mask has one entry for each level. -/
theorem length_mask : x.mask.length = x.L := length_unrank ..

/-- The output string has one digit for each level. -/
theorem length_digits : x.digits.length = x.L := length_outDigits.trans length_mask

variable (C : OutDigitsPre lim μ x)

include C in
/-- The digit at a level of the subset. -/
theorem getD_digits_inner (hl : l < x.L)
    (hb : x.mask.getD l false = true) : x.digits.getD l 0 = 9 :=
  getD_outDigits_of_true (count_unrank C.index_lt) (length_mask.symm ▸ hl) hb

include C in
/-- The digit at a level outside the subset, and the room behind the pointer. -/
theorem getD_digits_outer (hl : l < x.L)
    (hb : x.mask.getD l false = false) :
    (x.mask.take l).count false < x.L - x.m ∧
      x.digits.getD l 0 = 3 * x.rI.getD ((x.mask.take l).count false) 0
        + x.rJ.getD ((x.mask.take l).count false) 0 := by
  have hl' := length_mask.symm ▸ hl
  have hcount := count_false_unrank C.index_lt
  exact ⟨hcount ▸ List.count_take_lt hl' false hb,
    getD_outDigits_of_false (C.lenI.trans hcount.symm) (C.lenJ.trans hcount.symm) hl' hb⟩

include C in
/-- The mask of the subset lies inside the table of the K0² masks. -/
theorem base_add_le : x.base + x.L < lim.space := by
  have := Nat.mul_add_le_mul (Nat.mul_add_lt_mul C.gI_lt C.gJ_lt) (le_refl x.L)
  have := C.spaceMasks
  unfold OutDigitsArgs.base
  omega

/-! ## The invariant and the two branches -/

/-- The state before level l: the first l digits have been written, and no cell outside wd has
changed. -/
def Inv (μ : Light.Memory) (x : OutDigitsArgs) (l : ℕ) (σ : State) : Prop :=
  ∃ μ' : Light.Memory,
    σ = ⟨frame [x.gI, x.gJ, x.dI, x.dJ, x.aMASK, x.k0, x.L, x.wd, x.base, l,
      (x.mask.take l).count false], μ'⟩ ∧
    SegN μ' x.wd (x.digits.take l) ∧ SameOutside μ μ' x.wd x.L

include C in
/-- The cell of the mask that the test of level l reads. -/
theorem read_mask {μ'} (same : SameOutside μ μ' x.wd x.L)
    (hl : l < x.L) : μ' (x.base + l) = if x.mask.getD l false then 1 else 0 := by
  have hlen := length_mask (x := x)
  have  := C.apartMask
  rw [same (x.base + l) (by omega), C.segMask.read (by simp [hlen, hl]),
    List.getD_eq_getElem _ _ (by simp [hlen, hl]), List.getElem_map,
    List.getD_eq_getElem _ _ (by omega)]
  split_ifs <;> rfl

variable (h : Inv μ x l σ) (hl : l < x.L)

include C h hl in
/-- wd[level] := 9; level := level + 1. -/
theorem inner
    (hb : x.mask.getD l false = true) : levelInner.Runs lim σ (Inv μ x (l + 1)) := by
  obtain ⟨μ', rfl, seg, same⟩ := h
  light_facts C C.std
  have hnext := seg.take_succ (length_digits.symm ▸ hl)

  rw [getD_digits_inner C hl hb] at hnext
  refine ⟨by light_side [levelInner], _, ?_, hnext,
    same.update ⟨by omega, by omega⟩ _⟩
  simp [levelInner, update_frame_setLocal, (by
    rw [List.count_take_succ_getD x.mask false (length_mask.symm ▸ hl) false, hb]
    rfl
   : (x.mask.take (l + 1)).count false = (x.mask.take l).count false)]

include C h hl in
/-- wd[level] := 3 dI[outer] + dJ[outer]; outer := outer + 1; level := level + 1. -/
theorem outer
    (hb : x.mask.getD l false = false) : levelOuter.Runs lim σ (Inv μ x (l + 1)) := by
  obtain ⟨μ', rfl, seg, same⟩ := h
  light_facts C C.std
  obtain ⟨hlt, hdigit⟩ := getD_digits_outer C hl hb
  -- the two digits that the level reads
  have hreadI : μ' (x.dI + (x.mask.take l).count false)
      = (x.rI.getD ((x.mask.take l).count false) 0 : ℤ) := by
    rw [same _ (by omega)]
    exact C.segI.read (by omega)
  have hreadJ : μ' (x.dJ + (x.mask.take l).count false)
      = (x.rJ.getD ((x.mask.take l).count false) 0 : ℤ) := by
    rw [same _ (by omega)]
    exact C.segJ.read (by omega)
  have hI3 : x.rI.getD ((x.mask.take l).count false) 0 < 3 :=
    List.getD_of_forall_mem (by norm_num) C.ltI _
  have hJ3 : x.rJ.getD ((x.mask.take l).count false) 0 < 3 :=
    List.getD_of_forall_mem (by norm_num) C.ltJ _
  have hnext := seg.take_succ (length_digits.symm ▸ hl)

  rw [hdigit] at hnext
  generalize x.rI.getD ((x.mask.take l).count false) 0 = a at hreadI hI3 hnext
  generalize x.rJ.getD ((x.mask.take l).count false) 0 = b at hreadJ hJ3 hnext
  refine ⟨by light_side [levelOuter, hreadI, hreadJ], _, ?_, hnext,
    same.update ⟨by omega, by omega⟩ _⟩
  simp [levelOuter, update_frame_setLocal, (by
    rw [List.count_take_succ_getD x.mask false (length_mask.symm ▸ hl) false, if_pos hb]
   : (x.mask.take (l + 1)).count false = (x.mask.take l).count false + 1), hreadI, hreadJ]

/-- The walk along the mask writes the digits of the output string. -/
theorem walk {P} {d} (C : OutDigitsPre lim μ x) :
    Ends lim P d outDigitsWalk
      ⟨frame [x.gI, x.gJ, x.dI, x.dJ, x.aMASK, x.k0, x.L, x.wd, x.base, 0, 0], μ⟩
      (40 * x.L + 4) fun σ' => SegN σ'.mem x.wd x.digits ∧ SameOutside μ σ'.mem x.wd x.L := by
  light_facts C.std
  have  := base_add_le C
  refine Ends.whileBlock (Inv μ x) x.L ?start ?round ?done
    (by simp [levelInner, levelOuter]; omega)
  case start => exact ⟨μ, rfl, by simp [SegN, Seg], .refl⟩
  case round =>
    rintro l σ hl hI
    have hinner := inner C hI hl
    have houter := outer C hI hl
    obtain ⟨μ', rfl, -, same⟩ := hI
    have hread := read_mask C same hl
    refine ⟨by simp, by simpa using hl, ?_⟩
    -- if mask[level] = 1
    by_cases hb : x.mask.getD l false = true
    · rw [if_pos hb] at hread
      exact .ite_pos (hinner hb) (by simp [hread]) (by light_side)
    · rw [if_neg hb] at hread
      exact .ite_neg (houter (by simpa using hb)) (by simp [hread])
        (by light_side)
  case done =>
    rintro _ ⟨μ', rfl, seg, same⟩
    rw [List.take_of_length_le length_digits.le] at seg
    exact ⟨by simp, by simp, seg, same⟩

include C in
/-- The numbers on the way to the address of the mask fit in a word. -/
theorem index_le : x.gI * x.k0 + x.gJ ≤ lim.space := by

  have hbase := base_add_le C
  unfold OutDigitsArgs.base at hbase
  rcases Nat.eq_zero_or_pos x.L with h0 | hL
  ram_safe

end OutDigits

open OutDigits in
/-- **outDigits** meets its specification. -/
theorem outDigits_spec {lim } {P }
    (hP : P[52]? = some outDigitsBody) : OutDigitsSpec lim P := by
  intro x μ C
  refine fun d _ => ⟨outDigitsBody, hP, ?_⟩
  have  := C.std.space_le
  have  := index_le C

  have hprod := base_add_le C
  have haddr : (x.base : ℤ) ≤ lim.space := by omega
  have  : (0 : ℤ) ≤ ((x.gI : ℤ) * x.k0 + x.gJ) * x.L := by positivity
  unfold OutDigitsArgs.base at haddr
  push_cast at hprod haddr
  unfold tOutDigits
  -- mask := aMASK + (gI K0 + gJ) L
  light_set x.base using OutDigitsArgs.base
  -- level := 0; outer := 0; the walk
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  exact (walk C).mono (by simp; omega) fun _ h => h

end Light.Sec4
