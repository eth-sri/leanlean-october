/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Programs.Sec2.Theorem5.Contracts

/-!
# Tables of digits, by an odometer

The programs for Theorem 5 turn the number of a row or of a column into a string ("locate the output
strings", in the proof of Theorem 5), so they need the digits of these numbers in base 3 and in
base 4. digits(n, b, len, dst) writes, for every x < n, the len digits of x % b^len in base b, most
significant first, to the len cells from dst + x * len.  There is no division: row 0 is zero, and
row x + 1 is row x plus one, formed from the least significant digit on with a carry.

* The pure side: `carryInto b j x` is the carry into the place of weight b^j when 1 is added to x,
  defined as the routine computes it, and `placeDigit_succ` says that a place of x plus its carry,
  reduced if it reaches b, is the place of x + 1.
* `digitsPlace_spec` treats one place, `digitsInner_spec` one row, `digitsZero_spec` row 0, and
  `digits_spec` runs through the rows; `digits_entry` is the specification that the callers of the
  procedure assume.
-/

@[expose] public section



namespace Light.Sec2

namespace Digits

/-! ## Adding 1 to a number, place by place -/

/-- The digit of weight b^j of x. -/
def placeDigit (b j x : ℕ) := x / b ^ j % b

/-- The carry into the digit of weight b^j when 1 is added to x: 1 into the last place, and then 1
as long as the digit plus the carry reaches b. -/
def carryInto b
  | 0, _ => 1
  | j + 1, x => if placeDigit b j x + carryInto b j x < b then 0 else 1

/-- A digit is less than the base. -/
private theorem placeDigit_lt {b} (hb : 0 < b) j x : placeDigit b j x < b :=
  Nat.mod_lt _ hb

/-- A carry is 0 or 1. -/
private theorem carryInto_le_one b j x : carryInto b j x ≤ 1 := by
  cases j with
  | zero => exact le_rfl
  | succ j =>
    grind [carryInto]

/-- Adding a carry c to q: the last digit of q grows by c, or becomes 0 and gives a carry. -/
private theorem add_carry {b} (hb : 0 < b) q {c} (hc : c ≤ 1) :
    (q + c) / b = q / b + (if q % b + c < b then 0 else 1) ∧
      (q + c) % b = if q % b + c < b then q % b + c else 0 := by
  have hlt := Nat.mod_lt q hb
  obtain rfl | rfl : c = 0 ∨ c = 1 := by omega
  · simp [hlt]
  · grind [Nat.succ_div_mod_of_lt, Nat.succ_div_mod_of_eq]

/-- The digits of x + 1 from the place of weight b^j on are those of x plus the carry. -/
private theorem succ_div_pow {b} (hb : 0 < b) j x :
    (x + 1) / b ^ j = x / b ^ j + carryInto b j x := by
  induction j with
  | zero => simp [carryInto]
  | succ j ih =>
    rw [pow_succ, ← Nat.div_div_eq_div_mul, ih, (add_carry hb _ (carryInto_le_one b j x)).1,
      Nat.div_div_eq_div_mul]
    rfl

/-- **One place of the odometer.**  The digit of x + 1 is the digit of x plus the carry, or 0 if
this reaches b. -/
theorem placeDigit_succ {b} (hb : 0 < b) j x :
    placeDigit b j (x + 1) =
      if placeDigit b j x + carryInto b j x < b then placeDigit b j x + carryInto b j x else 0 := by
  grind [succ_div_pow, add_carry, carryInto_le_one, placeDigit]

/-- The digits below place len do not change when the number is reduced modulo b^len. -/
private theorem mod_pow_div_mod (b c : ℕ) {j len} (hj : j < len) :
    c % b ^ len / b ^ j % b = c / b ^ j % b := by
  obtain ⟨e, rfl⟩ : ∃ e, len = j + (e + 1) := ⟨len - j - 1, by omega⟩
  rw [Nat.pow_add, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self b e.succ_ne_zero)]

/-- The entry number q of the row of x. -/
private theorem getElem_digitList {b len x q} (hq : q < len)
     h :
    (ThreeSumApsp.digitList b len (x % b ^ len))[q] = placeDigit b (len - 1 - q) x := by
  grind [mod_pow_div_mod, ThreeSumApsp.digitList, ThreeSumApsp.digit, placeDigit]

/-! ## The program -/

end Digits

open Digits

variable {lim : Limits} {P : Program} {d : ℕ}

/-- One place of the new row: the digit of the row before it plus the carry, or 0 if this reaches
b; in the second case the carry stays 1. -/
def digitsPlace :=
  .set 7 (v 7 -' k 1) ;;
  .set 9 (M (v 6 +' v 7) +' v 8) ;;
  .ite (v 9 <' v 1) (
    .store (v 5 +' v 7) (v 9) ;;
    .set 8 (k 0)) (
    .store (v 5 +' v 7) (k 0))

/-- The loop that forms one row from the row before it, from the last place on. -/
def digitsInner : Stmt := .while (k 0 <' v 7) digitsPlace

/-- One round of the loop over the rows. -/
def digitsRow :=
  .set 7 (v 2) ;;
  .set 8 (k 1) ;;
  digitsInner ;;
  .set 4 (v 4 +' k 1) ;;
  .set 6 (v 5) ;;
  .set 5 (v 5 +' v 2)

/-- Row 0 is zero.  The place is not set at the beginning: local variables that are not arguments
start at 0. -/
def digitsZero : Stmt :=
  .while (v 7 <' v 2) (
    .store (v 3 +' v 7) (k 0) ;;
    .set 7 (v 7 +' k 1))

/-- digits(n, b, len, dst). -/
def digitsBody : Stmt :=
  .ite (k 0 <' v 0) (
    digitsZero ;;
    .set 4 (k 1) ;;
    .set 6 (v 3) ;;
    .set 5 (v 3 +' v 2) ;;
    .while (v 4 <' v 0) digitsRow) .skip

namespace Digits

/-! ## One row from the row before it -/

/-- The memory after r places of the row of y + 1 have been written to the len cells from cur, from
the last place on; no other cell has changed. -/
def Placed μ b len cur y r (μ' : Light.Memory) :=
  (∀ j < r, μ' (cur + (len - 1 - j)) = placeDigit b j (y + 1)) ∧ SameOutside μ μ' cur len

/-- One more place. -/
theorem Placed.step {μ μ'} {b len cur y r} (h : Placed μ b len cur y r μ')
    (hr : r < len) :
    Placed μ b len cur y (r + 1)
      (Function.update μ' (cur + (len - 1 - r)) (placeDigit b r (y + 1))) := by
  refine ⟨fun j hj => ?_, h.2.update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  ram_safe

/-- The state after r places: the place is len - r, and the carry is the carry into place r. -/
def Inv μ (n b len dst row cur prev y r : ℕ) (σ : State) :=
  ∃ (x : ℤ) (μ' : Light.Memory),
    σ = ⟨frame [n, b, len, dst, row, cur, prev, (len - r : ℕ), carryInto b r y, x], μ'⟩ ∧
      Placed μ b len cur y r μ'

variable {μ : Light.Memory} {n b len dst row cur prev y : ℕ} {T : ℕ} {Q : State → Prop}

variable (std : Std lim) (hb : 2 ≤ b) (hbw : (b : ℤ) ≤ lim.word)
    (hcur : cur + len ≤ lim.space) (hprev : prev + len ≤ cur)
    (hrow : ∀ q < len, μ (prev + q) = placeDigit b (len - 1 - q) y)

include std hb hbw hcur hprev hrow in
/-- **One place** of the new row is written, and the carry into the next place is formed. -/
theorem digitsPlace_spec  {r} (hr : r < len)
    {σ} (h : Inv μ n b len dst row cur prev y r σ) :
    Ends lim P d digitsPlace σ digitsPlace.blockCost
      (Inv μ n b len dst row cur prev y (r + 1)) := by
  obtain ⟨x, μ', rfl, hI⟩ := h
  light_facts std
  have  := placeDigit_lt (show 0 < b by omega) r y
  have  := carryInto_le_one b r y

  have hstep := hI.step hr
  rw [show len - 1 - r = len - (r + 1) by omega, placeDigit_succ (show 0 < b by omega) r y] at hstep
  -- The digit of the row before has not been overwritten.
  have hread : μ' (prev + (len - (r + 1))) = placeDigit b r y := by
    rw [hI.2 _ (Or.inl (by omega)), hrow _ (by omega), show len - 1 - (len - (r + 1)) = r by omega]
  unfold digitsPlace
  -- Place := Place - 1; Digit := mem[Prev + Place] + Carry
  light_set (len - (r + 1) : ℕ)
  light_set (placeDigit b r y + carryInto b r y : ℕ) using hread
  -- if Digit < b
  refine Ends.iteLast (fun hc => ?_) fun hc => ?_
  · -- No carry out of this place: mem[Cur + Place] := Digit; Carry := 0
    have hlt : placeDigit b r y + carryInto b r y < b := by simp at hc; omega
    rw [if_pos hlt] at hstep
    refine Ends.storeToThen (cur + (len - (r + 1))) ((placeDigit b r y + carryInto b r y : ℕ) : ℤ)
      (Ends.setTo ((0 : ℕ) : ℤ) ⟨((placeDigit b r y + carryInto b r y : ℕ) : ℤ), _, ?_, hstep⟩)
    rw [carryInto, if_pos hlt]
    rfl
  · -- A carry out of this place, so the carry into it was 1 and stays: mem[Cur + Place] := 0
    have hlt : ¬ placeDigit b r y + carryInto b r y < b := by simp at hc; omega
    rw [if_neg hlt] at hstep
    refine Ends.storeTo (cur + (len - (r + 1))) ((0 : ℕ) : ℤ)
      ⟨((placeDigit b r y + carryInto b r y : ℕ) : ℤ), _, ?_, hstep⟩
    rw [carryInto, if_neg hlt, show carryInto b r y = 1 by omega]
    rfl

include std hb hbw hcur hprev hrow in
/-- **One row**: the loop over the places writes the row of y + 1 to the len cells from cur, from
the row of y in the len cells from prev. -/
theorem digitsInner_spec  {x₀}
    (done : ∀ (c x ) (μ' : Light.Memory),
      (∀ q < len, μ' (cur + q) = placeDigit b (len - 1 - q) (y + 1)) →
      SameOutside μ μ' cur len → Q ⟨frame [n, b, len, dst, row, cur, prev, 0, c, x], μ'⟩)
    (hT : 26 * len + 4 ≤ T) :
    Ends lim P d digitsInner ⟨frame [n, b, len, dst, row, cur, prev, len, 1, x₀], μ⟩ T Q := by
  refine Ends.whileConst (Inv μ n b len dst row cur prev y) len digitsPlace.blockCost ?start ?round
    ?done
    (by simp [digitsPlace]; omega)
  case start => exact ⟨x₀, μ, rfl, fun j hj => absurd hj (by omega), .refl⟩
  case round =>
    intro r σ hr h
    have hplace := digitsPlace_spec (P := P) (d := d) std hb hbw hcur hprev hrow hr h
    obtain ⟨x, μ', rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hplace⟩
  case done =>
    rintro _ ⟨x, μ', rfl, hcells, same⟩
    refine ⟨by light_side, by light_side, ?_⟩
    grind

/-! ## The loop over the rows -/

/-- The state after the rows 0, …, i have been written: they stand in the table, and no cell outside
the table has changed. -/
def RowsDone μ (n b len dst i : ℕ) (σ : State) :=
  ∃ (p c x : ℤ) (μ' : Light.Memory), σ = ⟨frame [n, b, len, dst, (i + 1 : ℕ), (dst + (i + 1) * len : ℕ),
      (dst + i * len : ℕ), p, c, x], μ'⟩ ∧
    (∀ y < i + 1, ∀ q < len, μ' (dst + y * len + q) = (placeDigit b (len - 1 - q) y : ℕ)) ∧
    SameOutside μ μ' dst (n * len)

/-- The time of one round of the loop over the rows. -/
def tRow len := 26 * len + 18

/-- **One round of the loop over the rows** writes row `i + 1`, the digits of `i + 1`, from row
`i`. -/
theorem digitsRow_spec (std : Std lim) (hb : 2 ≤ b) (hbw : (b : ℤ) ≤ lim.word)
    (hsp : dst + n * len ≤ lim.space) (hnw : (n : ℤ) ≤ lim.word) {i} (hi : i + 1 < n)
    {σ} (h : RowsDone μ n b len dst i σ) :
    Ends lim P d digitsRow σ (tRow len) (RowsDone μ n b len dst (i + 1)) := by
  obtain ⟨p, c, x, μ', rfl, hrows, same⟩ := h
  light_facts std
  have  : (i + 1) * len + len ≤ n * len := Nat.mul_add_le_mul hi le_rfl
  have  : (i + 1) * len = i * len + len := Nat.succ_mul i len
  unfold digitsRow tRow
  -- Place := len; Carry := 1
  light_set len
  light_set 1
  -- while 0 < Place
  refine Ends.next _ (digitsInner_spec (y := i) std hb hbw (by omega) (by omega)
    (fun q hq => hrows i (by omega) q hq) ?_ le_rfl)
  intro c' x' μ'' hnew same'
  -- Row := Row + 1; Prev := Cur; Cur := Cur + len
  light_set (i + 1 + 1 : ℕ)
  light_set (dst + (i + 1) * len : ℕ)
  light_set (dst + (i + 1 + 1) * len : ℕ) using Nat.succ_mul
  refine ⟨_, _, _, _, rfl, fun y hy q hq => ?_,
      same.trans (same'.mono (by omega) (by omega))⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hy with hy | rfl
  · -- An earlier row lies before the cells that were written.
    have  : y * len + len ≤ (i + 1) * len := Nat.mul_add_le_mul hy le_rfl
    rw [same' _ (Or.inl (by omega))]
    exact hrows y hy q hq
  · exact hnew q hq

/-- **Row 0** is zero. -/
theorem digitsZero_spec (std : Std lim) (hsp : dst + len ≤ lim.space)
    (done : Q ⟨frame [n, b, len, dst, 0, 0, 0, len], wrote μ dst (fun _ => 0) len⟩)
    (hT : 13 * len + 4 ≤ T) :
    Ends lim P d digitsZero ⟨frame [n, b, len, dst], μ⟩ T Q := by
  light_facts std
  -- while Place < len
  refine Ends.whileBlock (fun q σ => σ =
    ⟨frame [n, b, len, dst, 0, 0, 0, q], wrote μ dst (fun _ => 0) q⟩) len ?start ?round ?done
  case start =>
    -- The place starts at 0.
    rw [wrote_zero, ← frame_append_zeros _ 4]
    rfl
  case round =>
    rintro q _ hq rfl
    -- mem[dst + Place] := 0; Place := Place + 1
    exact ⟨by light_side, by light_side, by light_side,
      by simp [update_frame_setLocal, ← wrote_succ]⟩
  case done =>
    simp_all

end Digits

variable {μ : Light.Memory} {n b len dst : ℕ}

/-- **digits** writes the table of digits and changes nothing else. -/
theorem digits_spec (std : Std lim) (hsp : dst + n * len ≤ lim.space) (hb : 2 ≤ b)
    (hbw : (b : ℤ) ≤ lim.word) (hnw : (n : ℤ) ≤ lim.word) :
    Ends lim P d digitsBody ⟨frame [n, b, len, dst], μ⟩ (60 * ((n + 1) * (len + 1))) fun σ' =>
      (∀ x < n, SegN σ'.mem (dst + x * len) (ThreeSumApsp.digitList b len (x % b ^ len))) ∧
        SameOutside μ σ'.mem dst (n * len) := by
  light_facts std
  -- if 0 < n
  refine Ends.iteLast (fun hpos => ?_) fun hzero => Ends.skip
    ⟨fun x hx => absurd hx (by simp at hzero; omega), .refl⟩
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by simp at hpos; omega⟩
  have hlen : (t + 1) * len = t * len + len := Nat.succ_mul t len
  -- Row 0.
  refine Ends.next _ (digitsZero_spec std (by omega) ?_ le_rfl) (by simp; ring_nf; omega)
  -- Row := 1; Prev := dst; Cur := dst + len, written as the invariant at i = 0 has them
  light_set (0 + 1 : ℕ)
  light_set (dst + 0 * len : ℕ)
  light_set (dst + 0 + 1 * len : ℕ)
  -- while Row < n; the n - 1 rounds take (n - 1) (26 len + 22) steps
  refine Ends.whileConst (RowsDone μ (t + 1) b len dst) t (tRow len) ?start ?round ?done
    (by simp [tRow]; ring_nf; omega)
  case start =>
    refine ⟨len, 0, 0, wrote μ dst (fun _ => 0) len, ?_, fun y hy q hq => ?_,
      sameOutside_wrote (hlen ▸ Nat.le_add_left ..)⟩
    · -- The carry and the digit start at 0.
      rw [← frame_append_zeros _ 2]
      rfl
    · obtain rfl : y = 0 := by omega
      rw [Nat.zero_mul, Nat.add_zero, wrote_done hq]
      simp [placeDigit]
  case round =>
    intro i σ hi h
    have hrow := digitsRow_spec (P := P) (d := d) std hb hbw hsp hnw (by omega) h
    obtain ⟨p, c, x, μ', rfl, -⟩ := h
    exact ⟨by light_side, by light_side, hrow⟩
  case done =>
    rintro _ ⟨p, c, x, μ', rfl, hrows, same⟩
    refine ⟨by light_side, by light_side, fun y hy q hq => ?_, same⟩
    have hq' := by simpa [ThreeSumApsp.digitList] using hq
    rw [List.getElem_map, getElem_digitList hq']
    exact hrows y hy q hq'

/-- **The specification that the callers of digits assume.** -/
theorem digits_entry (std : Std lim) (hP : P[pDigits]? = some digitsBody) {c} (hc : 60 ≤ c) :
    DigitsSpec lim P c :=
  fun _ _ _ _ _ hsp hb hbw hnw _ _ => .mono_const (.of_body hP (digits_spec std hsp hb hbw hnw)) hc

end Light.Sec2
