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
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.FrontFacts
public import ThreeSumApsp.Spec.Sec3.Theorem21a.Passes
public import ThreeSumApsp.Spec.Sec3.Theorem21b.NegativeTriangle

/-!
# 3SUM from Convolution-3SUM: binary digits of the labels, and selection by digits

Theorem 21(a), after [CH20, Theorem 5.1].  The reduction for n numbers
splits the set of the values by one or two binary digits of the labels x + V (`ChanHe.splitA`,
`ChanHe.splitB`).  Two routines do this.

* pick copies the elements whose digits at one or two given positions have given values
  (`pick_spec`, with `pickRound_runs` for one round).  What it has written after the first i
  elements is `pickPart`, and `Pick.Ctx.step` says how one more element changes it, in terms of the
  cells that the program reads.
* bits writes the table of the binary digits of the labels, Λ cells for each element (`bits_spec`,
  with `bitsElem_ends` for one element).  It first computes 2^Λ by doubling (`bitsPow_ends`).  The
  digits of one label are found from the top down: the rest of the label is doubled, and the digit
  is 1 if the result reaches 2^Λ (`bitsRow_ends`).

Where the body of a loop is a block, the goal of a round is `s.Runs lim σ R`.  This is a pair, which
says that the block s, started in σ, stays within the limits, and that R holds of the state after
it.  A procedure returns what its local 0 holds at the end.
-/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.Spec ThreeSumApsp.ChanHe

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## pick -/

/-- What pick has written after it has seen the first i elements. -/
def pickPart Λ β β' (x x' two : ℤ) (L BT : List ℤ) i :=
  passList
    (fun i => decide (BT.getD (i * Λ + β) 0 = x ∧ (two = 0 ∨ BT.getD (i * Λ + β') 0 = x')))
    (fun i => L.getD i 0) (List.range L.length) i

/-- One more element: it is written if its digit β is x and, in case two is not 0, its digit β' is
x'. -/
theorem pickPart_succ Λ β β' x x' two {L} BT {i}
    (hi : i < L.length) :
    pickPart Λ β β' x x' two L BT (i + 1) =
      if BT.getD (i * Λ + β) 0 = x ∧ (two = 0 ∨ BT.getD (i * Λ + β') 0 = x') then
        pickPart Λ β β' x x' two L BT i ++ [L.getD i 0]
      else pickPart Λ β β' x x' two L BT i := by
  have hi' : i < (List.range L.length).length := by simpa using hi
  split_ifs with h
  · exact (passList_succ_of _ hi' (by simpa using h)).trans (by simp [pickPart, passList])
  · exact passList_succ_of_not _ hi' (by simpa using h)

/-- At the end all the selected elements are written. -/
theorem pickPart_length Λ β β' x x' two L BT :
    pickPart Λ β β' x x' two L BT L.length = pickList Λ β β' x x' two L BT := by
  have h := passList_length
    (fun i => decide (BT.getD (i * Λ + β) 0 = x ∧ (two = 0 ∨ BT.getD (i * Λ + β') 0 = x')))
    (fun i => L.getD i 0) (List.range L.length)
  rwa [List.length_range] at h



/-- The current element is selected. -/
def pickTake  :=
  .store (v 9 +' v 11) (M (v 1 +' v 10)) ;;
  .set 11 (v 11 +' k 1)


/-- The end of a round of pick. -/
def pickNext  :=
  .set 12 (v 12 +' v 3) ;;
  .set 10 (v 10 +' k 1)


/-- One round of pick. -/
def pickRound  :=
  .ite (M (v 12 +' v 4) =' v 5)
    (.ite (v 8 =' k 0) pickTake (.ite (M (v 12 +' v 6) =' v 7) pickTake .skip))
    .skip ;;
  pickNext


/-- pick(len, s, bt, Λ, β, x, β', x', two, out): len numbers stand at s, and the table of their
digits at bt.  Copies to out the numbers whose digit β is x and, unless two is 0, whose digit β' is
x', and returns how many there are. -/
def pickBody  :=
  .set 10 (k 0) ;;
  .set 11 (k 0) ;;
  .set 12 (v 2) ;;
  .while (v 10 <' v 0) pickRound ;;
  .set 0 (v 11)

/-- One more element, in terms of the cells that the program reads. -/
theorem Pick.Ctx.step {μ μ'} {s bt out Λ β β' i} {L BT}
    (C : Pick.Ctx lim μ s bt out Λ β β' L BT) (hsame : SameOutside μ μ' out L.length)
    (hi : i < L.length) x x' two :
    pickPart Λ β β' x x' two L BT (i + 1) =
      if μ' (bt + i * Λ + β) = x ∧ (two = 0 ∨ μ' (bt + i * Λ + β') = x') then
        pickPart Λ β β' x x' two L BT i ++ [μ' (s + i)]
      else pickPart Λ β β' x x' two L BT i := by
  light_facts C
  have  : i * Λ + Λ ≤ L.length * Λ := Nat.mul_add_le_mul hi le_rfl
  have hread : ∀ γ < Λ, μ' (bt + i * Λ + γ) = BT.getD (i * Λ + γ) 0 := fun γ hγ => by
    rw [hsame _ (by omega), Nat.add_assoc]
    exact C.segTable.getD (by omega) 0
  rw [hread β C.posA, hread β' C.posB, hsame (s + i) (by omega), C.segSrc.getD hi 0]
  exact pickPart_succ Λ β β' x x' two BT hi

/-- The invariant of the loop of pick before round number i: the elements selected among the first i
stand at out, no cell outside the output has changed, and Row holds the address bt + iΛ of the
digits of element i, which is called row. -/
def PickInv μ (s bt out Λ β β' : ℕ) x x' two L BT i
    (σ : State) :=
  ∃ (μ' : Light.Memory) (row : ℕ), row = bt + i * Λ ∧
    σ = ⟨frame [L.length, s, bt, Λ, β, x, β', x', two, out, i,
      (pickPart Λ β β' x x' two L BT i).length, row], μ'⟩ ∧
    Seg μ' out (pickPart Λ β β' x x' two L BT i) ∧ SameOutside μ μ' out L.length

/-- One round of pick keeps the invariant. -/
theorem pickRound_runs {μ} {s bt out Λ β β' i} {x x' two} {L BT}
    (C : Pick.Ctx lim μ s bt out Λ β β' L BT) (hi : i < L.length) {σ}
    (hI : PickInv μ s bt out Λ β β' x x' two L BT i σ) :
    pickRound.Runs lim σ (PickInv μ s bt out Λ β β' x x' two L BT (i + 1)) := by
  obtain ⟨μ', row, hrow, rfl, hseg, hsame⟩ := hI
  have hstep := C.step hsame hi x x' two
  rw [← hrow] at hstep
  have hnext : row + Λ = bt + (i + 1) * Λ := by nlinarith
  -- what the addresses are compared with
  light_facts C
  have  : (pickPart Λ β β' x x' two L BT i).length ≤ i := length_passList_le _ _ _ _
  have  : i * Λ + Λ ≤ L.length * Λ := Nat.mul_add_le_mul hi le_rfl
  by_cases hA : μ' (row + β) ≠ x
  · -- the first digit differs: pickNext
    rw [if_neg (by simp [hA])] at hstep
    exact ⟨by light_side [pickRound, pickNext, hA], μ', row + Λ, hnext,
      by simp [pickRound, pickNext, update_frame_setLocal, hA, hstep], hstep ▸ hseg, hsame⟩
  rw [not_not] at hA
  by_cases hsel : two = 0 ∨ μ' (row + β') = x'
  · -- selected, by the test of Two or by the second digit: pickTake ; pickNext
    rw [if_pos ⟨hA, hsel⟩] at hstep
    refine ⟨?safe, Function.update μ' (out + (pickPart Λ β β' x x' two L BT i).length) (μ' (s + i)),
      row + Λ, hnext, ?state, hstep ▸ hseg.snoc _, hsame.write (by omega) _⟩
    -- the two cases of the test `two = 0`
    case safe =>
      by_cases h2 : two = 0
      · simp [pickRound, pickTake, pickNext, hA, eq_true h2, Limits.Addr, abs_le]; omega
      · simp [pickRound, pickTake, pickNext, hA, h2, hsel.resolve_left h2, Limits.Addr, abs_le]
        omega
    case state =>
      by_cases h2 : two = 0
      · simp [pickRound, pickTake, pickNext, update_frame_setLocal, hA, eq_true h2, hstep]
      · simp [pickRound, pickTake, pickNext, update_frame_setLocal, hA, h2,
          hsel.resolve_left h2, hstep]
  · -- the second digit differs: pickNext
    rw [if_neg (by simp [hsel])] at hstep
    rw [not_or] at hsel
    exact ⟨by light_side [pickRound, pickNext, hA, hsel.1, hsel.2], μ',
      row + Λ, hnext,
      by simp [pickRound, pickNext, update_frame_setLocal, hA, hsel.1, hsel.2, hstep],
      hstep ▸ hseg, hsame⟩

/-- **pick** meets its specification. -/
theorem pick_spec {p} (hP : P[p]? = some pickBody) : PickSpec lim P p := by
  intro d s bt out Λ β β' x x' two L BT μ C
  light_facts C
  refine Meets.of_body hP ?_
  unfold tPick pickBody
  -- Idx := 0 ; Written := 0 ; Row := Table
  light_set (0 : ℕ)
  light_set (0 : ℕ)
  light_set bt
  -- while Idx < Len
  refine Ends.next _ (Ends.whileBlock (PickInv μ s bt out Λ β β' x x' two L BT) L.length
    ?start ?round ?done (hT := le_rfl)) (by ram_safe [pickRound, pickTake, pickNext])
  case start => exact ⟨μ, bt, by simp, rfl, by simp [pickPart, passList], .refl⟩
  case round =>
    intro i σ hi hI
    obtain ⟨μ', row, -, rfl, -⟩ := id hI
    exact ⟨by light_side, by light_side, pickRound_runs C hi hI⟩
  case done =>
    -- Len := Written
    rintro _ ⟨μ', row, -, rfl, hseg, hsame⟩
    rw [pickPart_length] at hseg
    exact ⟨by light_side, by light_side, Ends.setTo (pickList Λ β β' x x' two L BT).length
      ⟨rfl, hseg, hsame⟩ (by simp [pickPart_length])
      (by simp [pickRound, pickTake, pickNext]; omega)⟩

/-! ## bits -/

/-- The digits of z from position ℓ on stand in their cells of the row of Λ cells from row, and no
cell outside the row has changed. -/
structure DigitsFrom (μ μ' : Light.Memory) (row Λ z ℓ : ℕ) : Prop where
  /-- The digits from position ℓ on are written. -/
  digits : ∀ β, ℓ ≤ β → β < Λ → μ' (row + β) = if z.testBit β then 1 else 0
  /-- No cell outside the row has changed. -/
  same : SameOutside μ μ' row Λ

/-- One more digit is written. -/
theorem DigitsFrom.write {μ μ'} {row Λ z ℓ} (h : DigitsFrom μ μ' row Λ z (ℓ + 1))
    (hℓ : ℓ < Λ) {b} (hb : b = if z.testBit ℓ then 1 else 0) :
    DigitsFrom μ (Function.update μ' (row + ℓ) b) row Λ z ℓ := by
  refine ⟨fun β h₁ h₂ => ?_, h.same.write (by omega) _⟩
  by_cases hβ : β = ℓ
  · simp_all
  · ram_safe

/-- When all digits are written, the row holds them. -/
theorem DigitsFrom.seg {μ μ'} {row Λ z} (h : DigitsFrom μ μ' row Λ z 0) :
    Seg μ' row (bitRow Λ z) := fun β hβ => by
  ram_safe [bitRow]



/-- The power 2^Λ, by doubling. -/
def bitsPow  :=
  .set 7 (k 1) ;;
  .set 11 (k 0) ;;
  .while (v 11 <' v 3) (
    .set 7 (k 2 *' v 7) ;;
    .set 11 (v 11 +' k 1))


/-- The digits of one label, from the top down: the rest of the label is kept at the top of Λ bits;
it is doubled, and the digit is 1 if the result reaches 2^Λ. -/
def bitsRow : Stmt :=
  .while (v 8 <' v 9) (
    .set 9 (v 9 -' k 1) ;;
    .set 10 (k 2 *' v 10) ;;
    .ite (v 10 <' v 7) (.store (v 9) (k 0))
      (.store (v 9) (k 1) ;; .set 10 (v 10 -' v 7)))


/-- The digits of the label of the current element. -/
def bitsElem  :=
  .set 10 (M (v 1 +' v 6) +' v 2) ;;
  .set 9 (v 8 +' v 3) ;;
  bitsRow ;;
  .set 8 (v 8 +' v 3)


/-- bits(len, s, V, Λ, bt, fr): len numbers of absolute value at most V stand at s.  Writes the Λ
lowest binary digits of each label x + V to the table at bt. -/
def bitsBody  :=
  bitsPow ;;
  .set 8 (v 4) ;;
  .for 6 (v 0) bitsElem

/-- The invariant of the loop of bitsPow before round number j: Pow holds 2^j. -/
def BitsPowInv μ len s V bt fr (Λ j : ℕ) (σ : State) :=
  σ = ⟨frame [len, s, V, Λ, bt, fr, 0, 2 ^ j, 0, 0, 0, j], μ⟩

/-- bitsPow puts 2^Λ into Pow. -/
theorem bitsPow_ends {μ} {len s V bt fr} {Λ B : ℕ} (hB : 2 ^ Λ ≤ B)
    (hword : (B : ℤ) ≤ lim.word) :
    Ends lim P d bitsPow ⟨frame [len, s, V, Λ, bt, fr], μ⟩ (12 * Λ + 8)
      (· = ⟨frame [len, s, V, Λ, bt, fr, 0, 2 ^ Λ, 0, 0, 0, Λ], μ⟩) := by
  have  := mod_cast Nat.one_le_two_pow.trans hB
  unfold bitsPow
  -- Pow := 1 ; Cnt := 0
  light_set 1
  light_set (0 : ℕ)
  -- while Cnt < Width
  refine Ends.whileBlock (BitsPowInv μ len s V bt fr Λ) Λ ?start ?round ?done
  case start => simp [BitsPowInv]
  case round =>
    -- Pow := 2 * Pow ; Cnt := Cnt + 1
    rintro j _ hj rfl
    have hpow := (Nat.pow_le_pow_right (by norm_num) hj).trans hB
    have  : (2 : ℤ) ^ j * 2 ≤ B := mod_cast hpow
    have hj' := mod_cast Nat.lt_two_pow_self.le.trans hpow
    have : (0 : ℤ) < 2 ^ j := by positivity
    exact ⟨by light_side, by light_side, by light_side,
      by simp [BitsPowInv, update_frame_setLocal, pow_succ, mul_comm]⟩
  case done =>
    rintro _ rfl
    exact ⟨by light_side, by light_side, rfl⟩

/-- The invariant of the loop of bitsRow before round number t: the digits from position ℓ = Λ - t
on are written, Cur points to the cell of digit ℓ, and Rest holds the lower digits, moved up to the
top of Λ bits: the number (z mod 2^ℓ) 2^(Λ - ℓ), which is `prefR Λ ℓ z`. -/
def BitsRowInv μ len s V bt fr idx (row Λ z : ℕ) t (σ : State) :=
  ∃ (μ' : Light.Memory) (ℓ cur : ℕ), ℓ + t = Λ ∧ cur = row + ℓ ∧
    σ = ⟨frame [len, s, V, Λ, bt, fr, idx, 2 ^ Λ, row, cur, prefR Λ ℓ z, Λ], μ'⟩ ∧
    DigitsFrom μ μ' row Λ z ℓ

/-- bitsRow writes the digits of z into the row. -/
theorem bitsRow_ends {μ} {len s V bt fr idx} {row Λ z B : ℕ} (hz : z < 2 ^ Λ)
    (hB : 2 ^ Λ ≤ B) (hword : ((2 * B + 2 : ℕ) : ℤ) ≤ lim.word) (hw : (lim.space : ℤ) ≤ lim.word)
    (hrow : row + Λ ≤ lim.space) :
    Ends lim P d bitsRow
      ⟨frame [len, s, V, Λ, bt, fr, idx, 2 ^ Λ, row, (row + Λ : ℕ), z, Λ], μ⟩ (23 * Λ + 4)
      fun σ' => ∃ μ',
        σ' = ⟨frame [len, s, V, Λ, bt, fr, idx, 2 ^ Λ, row, row, prefR Λ 0 z, Λ], μ'⟩ ∧
        Seg μ' row (bitRow Λ z) ∧ SameOutside μ μ' row Λ := by
  have  : (2 : ℤ) ^ Λ ≤ B := mod_cast hB
  push_cast at hword
  unfold bitsRow
  -- while Row < Cur
  refine Ends.whileBlock (BitsRowInv μ len s V bt fr idx row Λ z) Λ ?start ?round ?done
    (by simp; omega)
  case start =>
    exact ⟨μ, Λ, row + Λ, rfl, rfl, by grind [prefR_start],
      fun β h₁ h₂ => absurd h₂ (by omega), .refl⟩
  case round =>
    -- Cur := Cur - 1 ; Rest := 2 * Rest
    rintro t _ ht ⟨μ', ℓ', cur, hℓ, hcur, rfl, hdig⟩
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ, ℓ' = ℓ + 1 := ⟨ℓ' - 1, by omega⟩
    have hfits := prefR_nonneg Λ (ℓ + 1) (z : ℤ)
    have hfits' := prefR_lt (show ℓ + 1 ≤ Λ by omega) (z : ℤ)
    have hstep := (pref_step (show ℓ + 1 ≤ Λ by omega) z).2
    have hbit := testBit_iff_shift (show ℓ + 1 ≤ Λ by omega) z
    generalize prefR Λ (ℓ + 1) z = r at hfits hfits' hstep hbit
    have hpred : ((cur - 1 : ℕ) : ℤ) = (cur : ℤ) - 1 := by omega
    have haddr : ((cur : ℤ) - 1).toNat = row + ℓ := by omega
    refine ⟨by light_side, by light_side, ?_⟩
    by_cases hc : 2 * r < 2 ^ Λ
    · -- the digit is 0: mem[Cur] := 0
      exact ⟨by light_side [hc], _, ℓ, cur - 1, by omega, by omega,
        by simp [update_frame_setLocal, hc, hpred, haddr, hstep, shiftR],
        hdig.write (b := 0) (by omega) (by simp_all)⟩
    · -- the digit is 1: mem[Cur] := 1 ; Rest := Rest - Pow
      exact ⟨by light_side [hc], _, ℓ, cur - 1, by omega, by omega,
        by simp [update_frame_setLocal, hc, hpred, haddr, hstep, shiftR],
        hdig.write (b := 1) (by omega) (by rw [if_pos (hbit.2 hc)])⟩
  case done =>
    rintro _ ⟨μ', ℓ, cur, hℓ, hcur, rfl, hdig⟩
    obtain rfl : ℓ = 0 := by omega
    obtain rfl : cur = row := hcur
    exact ⟨by light_side, by light_side, μ', rfl, hdig.seg, hdig.same⟩

/-- The invariant of the main loop of bits before round number i: the digits of the first i labels
stand at bt, no cell outside the table has changed, and Row holds the address bt + iΛ of the next
row. -/
def BitsInv μ (s V Λ bt fr : ℕ) (L : List ℤ) i (σ : State) :=
  ∃ (μ' : Light.Memory) (row : ℕ) (cur rest : ℤ), row = bt + i * Λ ∧
    σ = ⟨frame [L.length, s, V, Λ, bt, fr, i, 2 ^ Λ, row, cur, rest, Λ], μ'⟩ ∧
    Seg μ' bt (bitTable V Λ (L.take i)) ∧ SameOutside μ μ' bt (L.length * Λ)

/-- One round of the main loop of bits keeps the invariant. -/
theorem bitsElem_ends {μ} {s V Λ bt fr i} {L}
    (C : Bits.Ctx lim μ s V Λ bt L) (hi : i < L.length) {σ}
    (hI : BitsInv μ s V Λ bt fr L i σ) :
    Ends lim P d bitsElem σ (23 * Λ + 19) fun σ' => σ'.loc 6 = i ∧
      BitsInv μ s V Λ bt fr L (i + 1)
        { σ' with loc := Function.update σ'.loc 6 (i + 1) } := by
  obtain ⟨μ', row, cur, rest, hrow, rfl, hseg, hsame⟩ := hI
  -- where the regions lie

  light_facts C
  have  : i * Λ + Λ ≤ L.length * Λ := Nat.mul_add_le_mul hi le_rfl

  have hread := (hsame _ (by omega)).trans (C.seg.getD hi 0)
  have hfits := abs_le.1 (C.bounded.getElem hi)
  rw [← List.getD_eq_getElem _ 0 hi, ← hread] at hfits
  obtain ⟨z, hz⟩ : ∃ z, z = lab V (L.getD i 0) := ⟨_, rfl⟩
  have  : (z : ℤ) = μ' (s + i) + V := by
    rw [hz, ← hread]
    exact Int.toNat_of_nonneg (by omega)
  unfold bitsElem
  -- Rest := mem[Src + Idx] + Bound
  light_set z
  -- Cur := Row + Width
  light_set (row + Λ : ℕ)
  -- the digits of the label
  light_piece (bitsRow_ends (lim := lim) (z := z) (B := 4 * V + 4) (by omega) C.pow_le
    (by push_cast; omega) C.space_le (by omega)) with _ ⟨μ'', rfl, hrowSeg, hrowSame⟩
  -- Row := Row + Width
  light_set (row + Λ : ℕ)
  refine ⟨rfl, μ'', row + Λ, row, prefR Λ 0 z, by grind,
    by simp [update_frame_setLocal], ?_, hsame.trans (hrowSame.mono (by omega) (by omega))⟩
  have hlen : (bitTable V Λ (L.take i)).length = i * Λ := by
    ram_arith [length_bitTable]
  rw [List.take_succ_getD L hi 0, bitTable_append, seg_append, hlen, ← hrow, ← hz]
  exact ⟨hseg.keep, hrowSeg⟩

/-- **bits** meets its specification. -/
theorem bits_spec {p} (hP : P[p]? = some bitsBody) : BitsSpec lim P p := by
  intro d fr s bt V Λ L μ C
  light_facts C
  refine Meets.of_body hP ?_
  unfold tBits bitsBody
  -- Pow := 2 ^ Width
  light_piece (bitsPow_ends (lim := lim) (B := 4 * V + 4) C.pow_le
    (by push_cast; omega)) with _ rfl
  -- Row := Table
  light_set bt
  -- for Idx < Len
  have  := Nat.mul_le_mul_left L.length (show 1 + (23 * Λ + 19) + 7 ≤ 60 * Λ + 40 by omega)
  refine Ends.for (BitsInv μ s V Λ bt fr L) L.length (23 * Λ + 19) ?start ?round ?done ?bound
    (hT := by simp only [Expr.cost]; omega)
  case start =>
    exact ⟨μ, bt, 0, 0, by simp, by simp [update_frame_setLocal], by simp [bitTable], .refl⟩
  case round => grind [bitsElem_ends]
  case bound =>
    rintro i _ - - ⟨μ', row, cur, rest, -, rfl, -⟩
    light_side
  case done =>
    ram_aesop [Light.Sec3.ChanHe.BitsInv]

end Light.Sec3.ChanHe
