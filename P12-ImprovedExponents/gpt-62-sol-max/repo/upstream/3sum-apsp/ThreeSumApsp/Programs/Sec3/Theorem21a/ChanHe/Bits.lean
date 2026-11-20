/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Lib.Filter
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

open ThreeSumApsp.ChanHe

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## pick -/

namespace Pick
registers [Len, Src, Table, Width, PosA, DigitA, PosB, DigitB, Two, Out, Idx, Written]

def test : Guard :=
  let row := v Table +' v Idx *' v Width
  .both (.atom (M (row +' v PosA) =' v DigitA))
    (.either (.atom (v Two =' k 0)) (.atom (M (row +' v PosB) =' v DigitB)))
end Pick

open Pick in
def pickBody : Stmt :=
  filterPass Idx Len Out Written test (M (v Src +' v Idx)) ;; .set Len (v Written)

open Pick in
theorem pick_spec {p : ℕ} (hP : P[p]? = some pickBody) : PickSpec lim P p := by
  intro d s bt out Λ β β' x x' two L BT μ C
  let good i := decide (BT.getD (i * Λ + β) 0 = x ∧ (two = 0 ∨ BT.getD (i * Λ + β') 0 = x'))
  let part i := ((List.range i).filter good).map (fun i => L.getD i 0)
  light_facts C
  refine Meets.of_body hP ?_
  unfold pickBody
  refine Ends.next _ (Ends.filterPass _ _ (fun i D => D = part i) rfl ?_ ?_
    C.space_le C.spaceOut rfl rfl (hT := le_rfl)) (by light_time [filterStep, test, tPick])
  · intro i D ν hi hD H
    have il := Nat.mul_add_le_mul hi (le_refl Λ)
    have hread := (H.same (s + i) (by have := H.size; omega)).trans (C.segSrc.getD hi 0)
    have htab γ (hγ : γ < Λ) : ν (bt + i * Λ + γ) = BT.getD (i * Λ + γ) 0 := by
      rw [H.same _ (by have := H.size; omega), Nat.add_assoc]
      exact C.segTable.getD (by omega) 0
    have haddr (γ : ℕ) : ((bt : ℤ) + i * (Λ : ℤ) + γ).toNat = bt + i * Λ + γ := by
      simp only [← Int.natCast_mul, ← Int.natCast_add, Int.toNat_natCast]
    have h₁ := htab β C.posA
    have h₂ := htab β' C.posB
    suffices ∀ {ok : Bool}, ok = good i → part (i + 1) =
        if ok then part i ++ [L.getD i 0] else part i by
      subst D
      refine ⟨by light_side [test], by light_side, ?_, ?_⟩
      · intro h
        have he : good i = true := by simpa [test, good, haddr, h₁, h₂] using h
        simpa [hread] using (this he.symm).symm
      · intro h
        have he : good i = false := by simpa [test, good, haddr, h₁, h₂] using h
        simpa using (this he.symm).symm
    rintro ok rfl
    simp [part, List.range_succ, List.filter_append, List.map_append]
    split <;> simp_all
  · rintro D ν rfl H
    exact Ends.setLast ⟨rfl, H.seg, H.same.mono le_rfl (Nat.add_le_add_left H.size _)⟩
      (hT := by light_time [filterStep, test, tPick])

/-! ## bits -/

/-- The digits of z from position ℓ on stand in their cells of the row of Λ cells from row, and no
cell outside the row has changed. -/
structure DigitsFrom (μ μ' : ℕ → ℤ) (row Λ z ℓ : ℕ) : Prop where
  /-- The digits from position ℓ on are written. -/
  digits : ∀ β, ℓ ≤ β → β < Λ → μ' (row + β) = if z.testBit β then 1 else 0
  /-- No cell outside the row has changed. -/
  same : SameOutside μ μ' row Λ

/-- One more digit is written. -/
theorem DigitsFrom.write {μ μ' : ℕ → ℤ} {row Λ z ℓ : ℕ} (h : DigitsFrom μ μ' row Λ z (ℓ + 1))
    (hℓ : ℓ < Λ) {b : ℤ} (hb : b = if z.testBit ℓ then 1 else 0) :
    DigitsFrom μ (Function.update μ' (row + ℓ) b) row Λ z ℓ := by
  refine ⟨fun β h₁ h₂ => ?_, h.same.write (by omega) _⟩
  by_cases hβ : β = ℓ
  · rw [hβ, Function.update_self, hb]
  · rw [Function.update_of_ne (by omega)]
    exact h.digits β (by omega) h₂

/-- When all digits are written, the row holds them. -/
theorem DigitsFrom.seg {μ μ' : ℕ → ℤ} {row Λ z : ℕ} (h : DigitsFrom μ μ' row Λ z 0) :
    Seg μ' row (bitRow Λ z) := fun β hβ => by
  simp only [bitRow, List.getElem_map, List.getElem_range]
  exact h.digits β (Nat.zero_le β) (by simpa [bitRow] using hβ)

namespace Bits

/-- The locals of bits.  The arguments: len, s, V, Λ, bt and the free pointer, which is not used.
Then the counter, the power 2^Λ, the address of the digits of the current element, the address of
the current digit, the rest of the label, and the counter of the loop that computes the power. -/
registers [Len, Src, Bound, Width, Table, _, Idx, Pow, Row, Cur, Rest, Cnt]

end Bits

open Bits in
/-- The power 2^Λ, by doubling. -/
def bitsPow : Stmt :=
  .set Pow (k 1) ;;
  .set Cnt (k 0) ;;
  .while (v Cnt <' v Width) (
    .set Pow (k 2 *' v Pow) ;;
    .set Cnt (v Cnt +' k 1))

open Bits in
/-- The digits of one label, from the top down: the rest of the label is kept at the top of Λ bits;
it is doubled, and the digit is 1 if the result reaches 2^Λ. -/
def bitsRow : Stmt :=
  .while (v Row <' v Cur) (
    .set Cur (v Cur -' k 1) ;;
    .set Rest (k 2 *' v Rest) ;;
    .ite (v Rest <' v Pow) (.store (v Cur) (k 0))
      (.store (v Cur) (k 1) ;; .set Rest (v Rest -' v Pow)))

open Bits in
/-- The digits of the label of the current element. -/
def bitsElem : Stmt :=
  .set Rest (M (v Src +' v Idx) +' v Bound) ;;
  .set Cur (v Row +' v Width) ;;
  bitsRow ;;
  .set Row (v Row +' v Width)

open Bits in
/-- bits(len, s, V, Λ, bt, fr): len numbers of absolute value at most V stand at s.  Writes the Λ
lowest binary digits of each label x + V to the table at bt. -/
def bitsBody : Stmt :=
  bitsPow ;;
  .set Row (v Table) ;;
  .for Idx (v Len) bitsElem

/-- The invariant of the loop of bitsPow before round number j: Pow holds 2^j. -/
def BitsPowInv (μ : ℕ → ℤ) (len s V bt fr : ℤ) (Λ j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [len, s, V, Λ, bt, fr, 0, 2 ^ j, 0, 0, 0, j], μ⟩

/-- bitsPow puts 2^Λ into Pow. -/
theorem bitsPow_ends {μ : ℕ → ℤ} {len s V bt fr : ℤ} {Λ B : ℕ} (hB : 2 ^ Λ ≤ B)
    (hword : (B : ℤ) ≤ lim.word) :
    Ends lim P d bitsPow ⟨frame [len, s, V, Λ, bt, fr], μ⟩ (12 * Λ + 8)
      (· = ⟨frame [len, s, V, Λ, bt, fr, 0, 2 ^ Λ, 0, 0, 0, Λ], μ⟩) := by
  have hB1 : (1 : ℤ) ≤ B := by exact_mod_cast Nat.one_le_two_pow.trans hB
  unfold bitsPow
  -- Pow := 1 ; Cnt := 0
  light_steps
  -- while Cnt < Width
  refine Ends.whileBlock (BitsPowInv μ len s V bt fr Λ) Λ ?start ?round ?done
  case start => simp [BitsPowInv]
  case round =>
    -- Pow := 2 * Pow ; Cnt := Cnt + 1
    rintro j _ hj rfl
    have hpow : 2 ^ (j + 1) ≤ B := (Nat.pow_le_pow_right (by norm_num) hj).trans hB
    have hpow' : (2 : ℤ) ^ j * 2 ≤ B := by exact_mod_cast hpow
    have hj' : ((j + 1 : ℕ) : ℤ) ≤ B := by exact_mod_cast Nat.lt_two_pow_self.le.trans hpow
    have : (0 : ℤ) < 2 ^ j := by positivity
    push_cast at hj'
    exact ⟨by light_side, by light_side, by light_side,
      by simp [BitsPowInv, update_frame_setLocal, pow_succ, mul_comm]⟩
  case done =>
    rintro _ rfl
    exact ⟨by light_side, by light_side, rfl⟩

/-- The invariant of the loop of bitsRow before round number t: the digits from position ℓ = Λ - t
on are written, Cur points to the cell of digit ℓ, and Rest holds the lower digits, moved up to the
top of Λ bits: the number (z mod 2^ℓ) 2^(Λ - ℓ), which is `prefR Λ ℓ z`. -/
def BitsRowInv (μ : ℕ → ℤ) (len s V bt fr idx : ℤ) (row Λ z : ℕ) (t : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (ℓ cur : ℕ), ℓ + t = Λ ∧ cur = row + ℓ ∧
    σ = ⟨frame [len, s, V, Λ, bt, fr, idx, 2 ^ Λ, row, cur, prefR Λ ℓ z, Λ], μ'⟩ ∧
    DigitsFrom μ μ' row Λ z ℓ

/-- bitsRow writes the digits of z into the row. -/
theorem bitsRow_ends {μ : ℕ → ℤ} {len s V bt fr idx : ℤ} {row Λ z B : ℕ} (hz : z < 2 ^ Λ)
    (hB : 2 ^ Λ ≤ B) (hword : ((2 * B + 2 : ℕ) : ℤ) ≤ lim.word) (hw : (lim.space : ℤ) ≤ lim.word)
    (hrow : row + Λ ≤ lim.space) :
    Ends lim P d bitsRow
      ⟨frame [len, s, V, Λ, bt, fr, idx, 2 ^ Λ, row, ((row + Λ : ℕ) : ℤ), z, Λ], μ⟩ (23 * Λ + 4)
      fun σ' => ∃ μ',
        σ' = ⟨frame [len, s, V, Λ, bt, fr, idx, 2 ^ Λ, row, row, prefR Λ 0 z, Λ], μ'⟩ ∧
        Seg μ' row (bitRow Λ z) ∧ SameOutside μ μ' row Λ := by
  have hB' : (2 : ℤ) ^ Λ ≤ B := by exact_mod_cast hB
  push_cast at hword
  unfold bitsRow
  -- while Row < Cur
  refine Ends.whileBlock (BitsRowInv μ len s V bt fr idx row Λ z) Λ ?start ?round ?done
    (by simp; omega)
  case start =>
    exact ⟨μ, Λ, row + Λ, rfl, rfl, by rw [prefR_start (by positivity) (by exact_mod_cast hz)],
      fun β h₁ h₂ => absurd h₂ (by omega), .refl⟩
  case round =>
    -- Cur := Cur - 1 ; Rest := 2 * Rest
    rintro t _ ht ⟨μ', ℓ', cur, hℓ, hcur, rfl, hdig⟩
    obtain ⟨ℓ, rfl⟩ : ∃ ℓ, ℓ' = ℓ + 1 := ⟨ℓ' - 1, by omega⟩
    have hfits := prefR_nonneg Λ (ℓ + 1) (z : ℤ)
    have hfits' := prefR_lt (show ℓ + 1 ≤ Λ by omega) (z : ℤ)
    have hstep := (pref_step (show ℓ + 1 ≤ Λ by omega) (z : ℤ)).2
    have hbit := testBit_iff_shift (show ℓ + 1 ≤ Λ by omega) z
    generalize prefR Λ (ℓ + 1) (z : ℤ) = r at hfits hfits' hstep hbit
    have hpred : ((cur - 1 : ℕ) : ℤ) = (cur : ℤ) - 1 := by omega
    have haddr : ((cur : ℤ) - 1).toNat = row + ℓ := by omega
    refine ⟨by light_side, by light_side, ?_⟩
    by_cases hc : 2 * r < 2 ^ Λ
    · -- the digit is 0: mem[Cur] := 0
      exact ⟨by light_side [hc], _, ℓ, cur - 1, by omega, by omega,
        by simp [update_frame_setLocal, hc, hpred, haddr, hstep, shiftR],
        hdig.write (b := 0) (by omega) (by rw [if_neg fun h => hbit.1 h hc])⟩
    · -- the digit is 1: mem[Cur] := 1 ; Rest := Rest - Pow
      exact ⟨by light_side [hc], _, ℓ, cur - 1, by omega, by omega,
        by simp [update_frame_setLocal, hc, hpred, haddr, hstep, shiftR],
        hdig.write (b := 1) (by omega) (by rw [if_pos (hbit.2 hc)])⟩
  case done =>
    rintro _ ⟨μ', ℓ, cur, hℓ, hcur, rfl, hdig⟩
    obtain rfl : ℓ = 0 := by omega
    obtain rfl : cur = row := by omega
    exact ⟨by light_side, by light_side, μ', rfl, hdig.seg, hdig.same⟩

/-- The invariant of the main loop of bits before round number i: the digits of the first i labels
stand at bt, no cell outside the table has changed, and Row holds the address bt + iΛ of the next
row. -/
def BitsInv (μ : ℕ → ℤ) (s V Λ bt fr : ℕ) (L : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (row : ℕ) (cur rest : ℤ), row = bt + i * Λ ∧
    σ = ⟨frame [L.length, s, V, Λ, bt, fr, i, 2 ^ Λ, row, cur, rest, Λ], μ'⟩ ∧
    Seg μ' bt (bitTable V Λ (L.take i)) ∧ SameOutside μ μ' bt (L.length * Λ)

/-- One round of the main loop of bits keeps the invariant. -/
theorem bitsElem_ends {μ : ℕ → ℤ} {s V Λ bt fr i : ℕ} {L : List ℤ}
    (C : Bits.Ctx lim μ s V Λ bt L) (hi : i < L.length) {σ : State}
    (hI : BitsInv μ s V Λ bt fr L i σ) :
    Ends lim P d bitsElem σ (23 * Λ + 19) fun σ' => σ'.loc Bits.Idx = i ∧
      BitsInv μ s V Λ bt fr L (i + 1)
        { σ' with loc := Function.update σ'.loc Bits.Idx ((i : ℤ) + 1) } := by
  obtain ⟨μ', row, cur, rest, hrow, rfl, hseg, hsame⟩ := hI
  -- where the regions lie
  have hw := C.space_le
  light_facts C
  have hrows : i * Λ + Λ ≤ L.length * Λ := Nat.mul_add_le_mul hi le_rfl
  have hnext : row + Λ = bt + (i + 1) * Λ := by rw [hrow, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have hread : μ' (s + i) = L.getD i 0 := (hsame _ (by omega)).trans (C.seg.getD hi 0)
  have hfits := abs_le.1 (C.bounded.getElem hi)
  rw [← List.getD_eq_getElem _ 0 hi, ← hread] at hfits
  obtain ⟨z, hz⟩ : ∃ z, z = lab V (L.getD i 0) := ⟨_, rfl⟩
  have hlab : (z : ℤ) = μ' (s + i) + V := by
    rw [hz, ← hread]
    exact Int.toNat_of_nonneg (by omega)
  unfold bitsElem
  -- Rest := mem[Src + Idx] + Bound
  light_set z
  -- Cur := Row + Width
  light_set (row + Λ : ℕ)
  -- the digits of the label
  light_piece (bitsRow_ends (lim := lim) (z := z) (B := 4 * V + 4) (by omega) C.pow_le
    (by push_cast; omega) hw (by omega)) with _ ⟨μ'', rfl, hrowSeg, hrowSame⟩
  -- Row := Row + Width
  light_set (row + Λ : ℕ)
  refine ⟨by simp, μ'', row + Λ, row, prefR Λ 0 z, hnext,
    by simp [update_frame_setLocal], ?_, hsame.trans (hrowSame.mono (by omega) (by omega))⟩
  have hlen : (bitTable V Λ (L.take i)).length = i * Λ := by
    rw [length_bitTable, List.length_take, min_eq_left hi.le]
  rw [List.take_succ_getD L hi 0, bitTable_append, seg_append, hlen, ← hrow, ← hz]
  exact ⟨hseg.keep, hrowSeg⟩

/-- **bits** meets its specification. -/
theorem bits_spec {p : ℕ} (hP : P[p]? = some bitsBody) : BitsSpec lim P p := by
  intro d fr s bt V Λ L μ C
  light_facts C
  refine Meets.of_body hP ?_
  unfold tBits bitsBody
  -- Pow := 2 ^ Width
  light_piece (bitsPow_ends (lim := lim) (B := 4 * V + 4) C.pow_le
    (by push_cast; omega)) with _ rfl
  -- Row := Table
  light_step
  -- for Idx < Len
  have htime := Nat.mul_le_mul_left L.length (show 1 + (23 * Λ + 19) + 7 ≤ 60 * Λ + 40 by omega)
  refine Ends.for (BitsInv μ s V Λ bt fr L) L.length (23 * Λ + 19) ?start ?round ?done ?bound
    (hT := by simp only [Expr.cost]; omega)
  case start =>
    exact ⟨μ, bt, 0, 0, by simp, by simp [update_frame_setLocal], by simp [bitTable], .refl⟩
  case round => exact fun i σ hi _ hI => bitsElem_ends C hi hI
  case bound =>
    rintro i _ - - ⟨μ', row, cur, rest, -, rfl, -⟩
    light_side
  case done =>
    rintro _ - ⟨μ', row, cur, rest, -, rfl, hseg, hsame⟩
    rw [List.take_length] at hseg
    exact ⟨hseg, hsame⟩

end Light.Sec3.ChanHe
