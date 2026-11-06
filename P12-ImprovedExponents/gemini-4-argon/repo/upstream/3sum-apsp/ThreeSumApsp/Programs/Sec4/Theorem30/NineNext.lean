module

public import ThreeSumApsp.Spec.Sec4.Theorem30.QueryLists
public import ThreeSumApsp.Util.List
public import Mathlib.Data.List.GetD
public import ThreeSumApsp.Lang.Lib.Pass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts

@[expose] public section

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The successor of a string, as two passes from left to right

`nineNext`, which goes from a string with a bounded number of nines to the next one, is defined by
recursion on the string.  A machine goes through the cells of a buffer from left to right.  This
file gives the function in that shape.

* One pass over the string finds the last position whose digit can be raised, and the number of
  nines before it (`nineScan`).
* A second pass writes the next string: the digits before that position are kept, its digit is
  raised by one, and the rest is filled with zeros followed by nines (`raiseAt`).

The result is `nineNext_eq_scan`.  It is proved in two steps: `nineNext` raises the last position
that can be raised (`raisePos`, `nineNext_eq_raise`), and the scan finds that position
(`nineScanFrom_eq`).  For the routine there are, besides, an invariant of the scan
(`nineScan_inv`) and the fact that the filling fits behind the position that is raised
(`raise_fits`).
-/


namespace ThreeSumApsp.Spec

/-! ## The last position that can be raised -/

/-- Whether the digit d can be raised when c nines come before it and at most hi nines are
allowed. -/
def canRaise (hi c d : ℕ) : Bool := decide (d < 8) || (decide (d = 8) && decide (c < hi))

/-- The last position of the string whose digit can be raised, with the number of nines before it;
c nines come before the string. -/
def raisePos (hi : ℕ) : ℕ → List ℕ → Option (ℕ × ℕ)
  | _, [] => none
  | c, d :: l =>
    match raisePos hi (if d = 9 then c + 1 else c) l with
    | some (p, c') => some (p + 1, c')
    | none => if canRaise hi c d then some (0, c) else none

/-- The string with the digit at position p raised by one and the least admissible filling behind
it; c nines come before p. -/
def raiseAt (lo p c : ℕ) (l : List ℕ) : List ℕ :=
  l.take p ++ (l.getD p 0 + 1) ::
    nineFirst (l.length - p - 1) (lo - c - if l.getD p 0 = 8 then 1 else 0)

/-- A digit that can be raised is at most 8. -/
theorem le_of_canRaise {hi c d : ℕ} (h : canRaise hi c d = true) : d ≤ 8 := by
  simp only [canRaise, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  omega

/-- What `nineNext` does to the first digit when the rest of the string cannot be raised. -/
theorem raise_head (lo hi c d : ℕ) (l : List ℕ) :
    nineRaise (lo - c) (hi - c) l.length d
      = (if canRaise hi c d then some (0, c) else none).map
          fun q : ℕ × ℕ => raiseAt lo q.1 q.2 (d :: l) := by
  rw [nineRaise]
  by_cases h8 : d < 8
  · simp [canRaise, h8, raiseAt, Nat.ne_of_lt h8]
  · by_cases h : d = 8 ∧ c < hi
    · simp [canRaise, h.1, h.2, raiseAt]
    · have hcan : canRaise hi c d = false := by
        simp only [canRaise, Bool.or_eq_false_iff, decide_eq_false_iff_not, Bool.and_eq_false_iff]
        exact ⟨h8, by tauto⟩
      rw [if_neg h8, if_neg fun h' => h ⟨h'.1, by omega⟩, hcan]
      rfl

/-- `nineNext` raises the last position that can be raised. -/
theorem nineNext_eq_raise (lo hi c : ℕ) (l : List ℕ) :
    nineNext (lo - c) (hi - c) l = (raisePos hi c l).map fun q => raiseAt lo q.1 q.2 l := by
  induction l generalizing c with
  | nil => rfl
  | cons d l ih =>
    have hlo : (if d = 9 then lo - c - 1 else lo - c) = lo - (if d = 9 then c + 1 else c) := by
      split_ifs <;> omega
    have hhi : (if d = 9 then hi - c - 1 else hi - c) = hi - (if d = 9 then c + 1 else c) := by
      split_ifs <;> omega
    rw [nineNext, raisePos, hlo, hhi, ih]
    rcases raisePos hi (if d = 9 then c + 1 else c) l with _ | ⟨p, c'⟩
    · exact raise_head lo hi c d l
    · simp [raiseAt]

/-! ## The scan from left to right -/

/-- The state of the scan: 1 if a position that can be raised has been seen, the last such
position, the number of nines before it, and the number of nines seen so far. -/
structure NineScan where
  found : ℕ
  pos : ℕ
  before : ℕ
  nines : ℕ

/-- One step of the scan: the cell number i holds the digit d. -/
def nineScanStep (hi i d : ℕ) (s : NineScan) : NineScan :=
  { found := if canRaise hi s.nines d then 1 else s.found
    pos := if canRaise hi s.nines d then i else s.pos
    before := if canRaise hi s.nines d then s.nines else s.before
    nines := if d = 9 then s.nines + 1 else s.nines }

/-- The scan of a list whose first cell has the number i. -/
def nineScanFrom (hi : ℕ) : ℕ → List ℕ → NineScan → NineScan
  | _, [], s => s
  | i, d :: l, s => nineScanFrom hi (i + 1) l (nineScanStep hi i d s)

/-- The state after the first j cells. -/
def nineScan (hi : ℕ) (l : List ℕ) (j : ℕ) : NineScan := nineScanFrom hi 0 (l.take j) ⟨0, 0, 0, 0⟩

/-- The scan of two lists one after the other: the second list is scanned from the state after the
first. -/
theorem nineScanFrom_append (hi i : ℕ) (l l' : List ℕ) (s : NineScan) :
    nineScanFrom hi i (l ++ l') s = nineScanFrom hi (i + l.length) l' (nineScanFrom hi i l s) := by
  induction l generalizing i s with
  | nil => rfl
  | cons d l ih =>
    rw [List.cons_append, nineScanFrom, nineScanFrom, ih, List.length_cons]
    congr 1
    omega

/-- The state after one more cell is one step of the scan from the state before that cell. -/
theorem nineScan_succ (hi : ℕ) (l : List ℕ) {j : ℕ} (hj : j < l.length) :
    nineScan hi l (j + 1) = nineScanStep hi j (l.getD j 0) (nineScan hi l j) := by
  rw [nineScan, nineScan, List.take_succ_getD l hj 0, nineScanFrom_append, List.length_take,
    Nat.min_eq_left hj.le, Nat.zero_add]
  rfl

/-- The scan finds the last position that can be raised. -/
theorem nineScanFrom_eq (hi i : ℕ) (l : List ℕ) (s : NineScan) :
    nineScanFrom hi i l s =
      match raisePos hi s.nines l with
      | some (p, c) => ⟨1, i + p, c, s.nines + l.count 9⟩
      | none => ⟨s.found, s.pos, s.before, s.nines + l.count 9⟩ := by
  induction l generalizing i s with
  | nil => rfl
  | cons d l ih =>
    have hn : (nineScanStep hi i d s).nines = if d = 9 then s.nines + 1 else s.nines := rfl
    have hcount : (if d = 9 then s.nines + 1 else s.nines) + l.count 9
        = s.nines + (d :: l).count 9 := by
      by_cases h : d = 9
      · rw [h, if_pos rfl, List.count_cons_self]
        omega
      · rw [if_neg h, List.count_cons_of_ne h]
    rw [nineScanFrom, ih, raisePos, hn, hcount]
    rcases raisePos hi (if d = 9 then s.nines + 1 else s.nines) l with _ | ⟨p, c⟩
    · by_cases hc : canRaise hi s.nines d <;> simp [nineScanStep, hc]
    · simp only [NineScan.mk.injEq, true_and, and_true]
      omega

/-- **The successor by two passes.**  After the scan of the whole string, either no position can be
raised and the string is the last one, or the next string is obtained by raising the position
found. -/
theorem nineNext_eq_scan (lo hi : ℕ) (l : List ℕ) :
    nineNext lo hi l =
      if (nineScan hi l l.length).found = 1 then
        some (raiseAt lo (nineScan hi l l.length).pos (nineScan hi l l.length).before l)
      else none := by
  have h := nineNext_eq_raise lo hi 0 l
  rw [Nat.sub_zero, Nat.sub_zero] at h
  rw [h, nineScan, List.take_length, nineScanFrom_eq]
  rcases raisePos hi 0 l with _ | ⟨p, c⟩ <;> simp

/-! ## What the scan has found -/

/-- What holds of the state s of the scan after j cells: the counter holds the number of nines
among them, and the position found, if any, is one of them, can be raised, and has the recorded
number of nines before it. -/
structure NineScanInv (hi : ℕ) (l : List ℕ) (j : ℕ) (s : NineScan) : Prop where
  nines : s.nines = (l.take j).count 9
  found : s.found = 0 ∨ s.found = 1
  pos_lt : s.found = 1 → s.pos < j
  canRaise : s.found = 1 → canRaise hi s.before (l.getD s.pos 0) = true
  before : s.found = 1 → s.before = (l.take s.pos).count 9

theorem nineScan_inv (hi : ℕ) (l : List ℕ) {j : ℕ} (hj : j ≤ l.length) :
    NineScanInv hi l j (nineScan hi l j) := by
  induction j with
  | zero => exact ⟨rfl, Or.inl rfl, nofun, nofun, nofun⟩
  | succ j ih =>
    have ih := ih (Nat.le_of_succ_le hj)
    rw [nineScan_succ hi l hj]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [nineScanStep]
    · rw [List.count_take_succ_getD l 9 hj 0, ← ih.nines]
      split_ifs <;> rfl
    · split_ifs
      · exact Or.inr rfl
      · exact ih.found
    · split_ifs
      · exact fun _ => Nat.lt_succ_self j
      · exact fun hf => (ih.pos_lt hf).trans (Nat.lt_succ_self j)
    · split_ifs with hc
      · exact fun _ => hc
      · exact ih.canRaise
    · split_ifs
      · exact fun _ => ih.nines
      · exact ih.before

/-! ## The filling fits -/

/-- Behind a position that can be raised there is room for the nines that are still needed. -/
theorem raise_fits {lo p : ℕ} {l : List ℕ} (hp : p < l.length) (h8 : l.getD p 0 ≤ 8)
    (hlo : lo ≤ l.count 9) : lo - (l.take p).count 9 ≤ l.length - p - 1 := by
  have : l.count 9 = (l.take p).count 9 + (l.drop p).count 9 := by
    rw [← List.count_append, List.take_append_drop]
  have : (l.drop p).count 9 = (l.drop (p + 1)).count 9 := by
    rw [List.drop_eq_getElem_cons hp, List.count_cons_of_ne]
    rw [List.getD_eq_getElem _ _ hp] at h8
    omega
  have hle := List.count_le_length (a := 9) (l := l.drop (p + 1))
  rw [List.length_drop] at hle
  omega

end ThreeSumApsp.Spec


/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The least string with a given number of nines

nineFirst(a, n, lo) writes n - lo zeros and then lo nines into the cells from a: the first string of
the enumeration `Spec.nineStrs n lo hi`.  The two loops that write zeros and then nines up to the
end of the string are also the end of nineNext, so they are a statement of their own, `fillTail`.

Each of the two loops writes one digit again and again while a test holds (`fillRun`,
`Ends.fillRun`).  Together they write the least string from the current position on
(`fillTail_spec`), and `nineFirst_spec` is the case of the position 0.
-/


namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Nine

/-- The local variables that nineFirst and nineNext share: the address of the string, its length,
the least number of nines, the current position, and the number of nines that are still to be
written.  Local 0 also takes the result. -/
abbrev Str : ℕ := 0
@[inherit_doc Str] abbrev Result : ℕ := 0
@[inherit_doc Str] abbrev Len : ℕ := 1
@[inherit_doc Str] abbrev MinNines : ℕ := 2
@[inherit_doc Str] abbrev Pos : ℕ := 4
@[inherit_doc Str] abbrev Need : ℕ := 10

end Nine

open Nine

/-! ## One digit again and again -/

/-- While the test holds: mem[str + pos] := c; pos := pos + 1. -/
def fillRun (test : Cond) (c : ℕ) : Stmt :=
  .while test (
    .store (v Str +' v Pos) (k c) ;;
    .set Pos (v Pos +' k 1))

/-- The cells that have been written hold the digit. -/
theorem segN_wrote_const (μ : ℕ → ℤ) (dst c n : ℕ) :
    SegN (wrote μ dst (fun _ => (c : ℤ)) n) dst (List.replicate n c) := fun i hi => by
  rw [wrote_done (by simpa using hi)]
  simp

/-- **The rule for fillRun.**  The test is safe and holds in the first cnt rounds and no longer; it
may depend on the position, not on the memory.  Then the digit c is written into cnt cells.  (A
constant up to 100 fits in a word.) -/
theorem Ends.fillRun (hs : Std lim) {test : Cond} {c a i₀ cnt T : ℕ} {loc μ : ℕ → ℤ}
    {Q : State → Prop} (hc : c ≤ 100) (ha : a + (i₀ + cnt) < lim.space) (hstr : loc Str = a)
    (hpos : loc Pos = i₀)
    (htest : ∀ j ≤ cnt, ∀ μ', test.Safe lim ⟨Function.update loc Pos ((i₀ + j : ℕ) : ℤ), μ'⟩ ∧
      (test.Holds ⟨Function.update loc Pos ((i₀ + j : ℕ) : ℤ), μ'⟩ ↔ j < cnt))
    (done : Q ⟨Function.update loc Pos ((i₀ + cnt : ℕ) : ℤ),
      wrote μ (a + i₀) (fun _ => (c : ℤ)) cnt⟩)
    (hT : cnt * (test.cost + 1 + 9) + (test.cost + 1) ≤ T := by light_time) :
    Ends lim P d (fillRun test c) ⟨loc, μ⟩ T Q := by
  light_facts hs
  refine Ends.whileBlock (fun j σ => σ = ⟨Function.update loc Pos ((i₀ + j : ℕ) : ℤ),
    wrote μ (a + i₀) (fun _ => (c : ℤ)) j⟩) cnt ?start ?round ?done hT
  case start => rw [wrote_zero, Nat.add_zero, ← hpos, Function.update_eq_self]
  case round =>
    rintro j _ hj rfl
    have haddr : ((a : ℤ) + ((i₀ : ℤ) + j)).toNat = a + i₀ + j := by omega
    refine ⟨(htest j hj.le _).1, (htest j hj.le _).2.mpr hj,
      by light_side [hstr], ?_⟩
    rw [← wrote_succ]
    simp [hstr, haddr, add_assoc]
  case done =>
    rintro _ rfl
    exact ⟨(htest cnt le_rfl _).1, fun h => absurd ((htest cnt le_rfl _).2.mp h) (lt_irrefl _),
      done⟩

/-! ## Zeros and then nines up to the end of the string -/

/-- Writes zeros from the current position on as long as more than need cells remain, and nines into
the remaining cells. -/
def fillTail : Stmt :=
  fillRun (v Pos +' v Need <' v Len) 0 ;;
  fillRun (v Pos <' v Len) 9

/-- fillTail writes the least string with need nines into the cells from the position i₀ on. -/
theorem fillTail_spec (hs : Std lim) {μ : ℕ → ℤ} {a n i₀ need : ℕ} (ha : a + n < lim.space)
    (hfit : i₀ + need ≤ n) (loc : ℕ → ℤ) (hstr : loc Str = a) (hlen : loc Len = n)
    (hpos : loc Pos = i₀) (hneed : loc Need = need) :
    Ends lim P d fillTail ⟨loc, μ⟩ (15 * (n - i₀) + 10) fun σ' =>
      σ'.loc = Function.update loc Pos n ∧ SegN σ'.mem (a + i₀) (nineFirst (n - i₀) need) ∧
        SameOutside μ σ'.mem (a + i₀) (n - i₀) := by
  have := hs.space_le
  have hmid : i₀ + (n - i₀ - need) = n - need := by omega
  -- zeros while pos + need < len
  refine Ends.next _ (Ends.fillRun hs (a := a) (i₀ := i₀) (cnt := n - i₀ - need) (by norm_num)
    (by omega) hstr hpos
    (fun j hj μ' => by light_side [hlen, hneed]) ?_ (hT := le_rfl)) (by simp; omega)
  -- nines while pos < len
  refine Ends.fillRun hs (a := a) (i₀ := n - need) (cnt := need) (by norm_num) (by omega)
    (by simpa using hstr) (by simp [hmid]) (fun j hj μ' => by simp [hlen]; omega) ?_
    (by simp; omega)
  -- the zeros are kept by the second loop, and both loops stay within the n - i₀ cells
  have hzeros := segN_wrote_const μ (a + i₀) 0 (n - i₀ - need)
  have hsame₀ : SameOutside μ (wrote μ (a + i₀) (fun _ => ((0 : ℕ) : ℤ)) (n - i₀ - need)) (a + i₀)
      (n - i₀ - need) := sameOutside_wrote le_rfl
  generalize wrote μ (a + i₀) (fun _ => ((0 : ℕ) : ℤ)) (n - i₀ - need) = μ₀ at hzeros hsame₀ ⊢
  have hsame₉ : SameOutside μ₀ (wrote μ₀ (a + (n - need)) (fun _ => ((9 : ℕ) : ℤ)) need)
      (a + (n - need)) need := sameOutside_wrote le_rfl
  refine ⟨by simp [Nat.sub_add_cancel (show need ≤ n by omega)], ?_,
    (hsame₀.mono le_rfl (by omega)).trans (hsame₉.mono (by omega) (by omega))⟩
  have hdst : a + i₀ + (List.map (fun x : ℕ => (x : ℤ)) (List.replicate (n - i₀ - need) 0)).length
      = a + (n - need) := by simp; omega
  rw [nineFirst, SegN, List.map_append, seg_append, hdst]
  exact ⟨hzeros.keep, segN_wrote_const _ _ 9 _⟩

/-! ## The least string -/

/-- nineFirst(str, len, minNines): the least string from the position 0 on. -/
def nineFirstBody : Stmt :=
  .set Pos (k 0) ;;
  .set Need (v MinNines) ;;
  fillTail

/-- **nineFirst** writes the least string of n digits with lo nines. -/
theorem nineFirst_spec (hP : P[Proc.nineFirst]? = some nineFirstBody) (hs : Std lim) :
    NineFirstSpec lim P := by
  intro a n lo μ hlo ha
  refine fun d _ => ⟨nineFirstBody, hP, ?_⟩
  have := hs.const_le
  unfold tNineFirst
  -- pos := 0; need := minNines
  light_set (0 : ℕ)
  light_set lo
  -- fillTail
  refine (fillTail_spec hs (i₀ := 0) (need := lo) ha (by omega) _ rfl rfl rfl rfl).mono
    (by simp; omega) ?_
  rintro σ' ⟨-, hseg, hsame⟩
  exact ⟨hseg, hsame⟩



/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The next string of the enumeration

nineNext(a, n, lo, hi) replaces the string of n digits at a by the next string with between lo and
hi nines (`Spec.nineNext`), and returns 1; if the string is the last one, it leaves it and
returns 0.  This is the step of all three enumerations of Section 4 (proof of Lemma 29: "Generating
the boxes with e stars […] also takes O(L) operations per box"; proof of Theorem 30: "Enumerating
them also takes O(L) operations per number").

There are two passes, as in `Spec.nineNext_eq_scan`.
1. The first pass finds the last position that can be raised and the number of nines before it.  One
   round is `Spec.nineScanStep` (`scanRound_runs`), so after i rounds the locals hold
   `Spec.nineScan hi l i` (`ScanInv`).
2. The second pass computes how many nines are needed behind that position (`needStmt_runs`), raises
   the digit and writes the least admissible filling behind it (`fillTail_spec`).  What stands in
   the memory then is `Spec.raiseAt` (`segN_raiseAt`).
-/





namespace Nine

/-- The further local variables of nineNext: the largest number of nines, the state of the scan
(whether a position that can be raised has been found, the last such position, the number of nines
before it, the number of nines seen so far), and a digit. -/
abbrev MaxNines : ℕ := 3
@[inherit_doc MaxNines] abbrev Found : ℕ := 5
@[inherit_doc MaxNines] abbrev Best : ℕ := 6
@[inherit_doc MaxNines] abbrev Before : ℕ := 7
@[inherit_doc MaxNines] abbrev Nines : ℕ := 8
@[inherit_doc MaxNines] abbrev Digit : ℕ := 9

end Nine


/-! ## The first pass -/

/-- Remember the current position and the number of nines before it. -/
def markStmt : Stmt := .set Found (k 1) ;; .set Best (v Pos) ;; .set Before (v Nines)

/-- If the digit can be raised, remember its position. -/
def raiseTest : Stmt :=
  .ite (v Digit <' k 8) markStmt
    (.ite (v Digit =' k 8) (.ite (v Nines <' v MaxNines) markStmt .skip) .skip)

/-- One round of the scan: read the digit at the current position, remember the position if the
digit can be raised, count the digit if it is a nine, and go on. -/
def scanRound : Stmt :=
  .set Digit (M (v Str +' v Pos)) ;;
  raiseTest ;;
  .ite (v Digit =' k 9) (.set Nines (v Nines +' k 1)) .skip ;;
  .set Pos (v Pos +' k 1)

theorem scanRound_cost : scanRound.blockCost = 35 := rfl

/-- The locals during the scan: the arguments, the position i, the state s of the scan, and the
digit read last. -/
def scanFrame (a n lo hi i : ℕ) (s : NineScan) (dg : ℕ) : ℕ → ℤ :=
  frame [a, n, lo, hi, i, s.found, s.pos, s.before, s.nines, dg]

/-- One round of the scan is `Spec.nineScanStep`. -/
theorem scanRound_runs (hs : Std lim) {μ : ℕ → ℤ} {a n lo hi i dg dg' : ℕ} {s : NineScan}
    (ha : a + n < lim.space) (hi' : i < n) (hcell : μ (a + i) = dg) (hnines : s.nines ≤ i) :
    scanRound.Runs lim ⟨scanFrame a n lo hi i s dg', μ⟩
      (· = ⟨scanFrame a n lo hi (i + 1) (nineScanStep hi i dg s) dg, μ⟩) := by
  light_facts hs
  have hcast8 : ((dg : ℤ) = 8) = (dg = 8) := by norm_cast
  have hcast9 : ((dg : ℤ) = 9) = (dg = 9) := by norm_cast
  simp only [scanRound, raiseTest, markStmt, scanFrame, nineScanStep, canRaise]
  -- The tests of the program tell five cases apart: the digit is below 8; it is 8, and one more
  -- nine is allowed or not; it is 9; it is above 9.  In each case the block is run: the first goal
  -- says that every address is in range and every value fits in a word, the second that the last
  -- state is the one stated.
  have hcases : (dg < 8 ∧ dg ≠ 8 ∧ dg ≠ 9) ∨ (dg = 8 ∧ s.nines < hi) ∨ (dg = 8 ∧ ¬ s.nines < hi) ∨
      dg = 9 ∨ (¬ dg < 8 ∧ dg ≠ 8 ∧ dg ≠ 9) := by omega
  rcases hcases with ⟨h₁, h₂, h₃⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl | ⟨h₁, h₂, h₃⟩ <;> constructor <;>
    simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
    omega

/-- Before round i the locals hold the state of the scan after i cells.  The memory is not
changed. -/
def ScanInv (a lo hi : ℕ) (l : List ℕ) (μ : ℕ → ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ dg : ℕ, σ = ⟨scanFrame a l.length lo hi i (nineScan hi l i) dg, μ⟩

/-! ## The second pass -/

/-- The digit at the position found, and the number of nines that have to be written behind it:
lo - before, less one if the digit becomes a nine, and not below 0. -/
def needStmt : Stmt :=
  .set Digit (M (v Str +' v Best)) ;;
  .set Need (v MinNines -' v Before) ;;
  .ite (v Digit =' k 8) (.set Need (v Need -' k 1)) .skip ;;
  .ite (v Need <' k 0) (.set Need (k 0)) .skip

theorem needStmt_cost : needStmt.blockCost = 23 := rfl

/-- needStmt computes the subtraction of natural numbers in `Spec.raiseAt`. -/
theorem needStmt_runs (hs : Std lim) {μ : ℕ → ℤ} {a n lo hi i dg dg' : ℕ} {s : NineScan}
    (ha : a + n < lim.space) (hp : s.pos < n) (hcell : μ (a + s.pos) = dg) (hlo : lo ≤ n)
    (hbefore : s.before ≤ n) :
    needStmt.Runs lim ⟨scanFrame a n lo hi i s dg', μ⟩
      (· = ⟨frame [a, n, lo, hi, i, s.found, s.pos, s.before, s.nines, dg,
        ((lo - s.before - (if dg = 8 then 1 else 0) : ℕ) : ℤ)], μ⟩) := by
  light_facts hs
  have hcast8 : ((dg : ℤ) = 8) = (dg = 8) := by norm_cast
  have hzero₁ : (lo : ℤ) - s.before - 1 < 0 → lo - s.before - 1 = 0 := by omega
  have hcast₁ : ¬ (lo : ℤ) - s.before - 1 < 0 →
      ((lo - s.before - 1 : ℕ) : ℤ) = (lo : ℤ) - s.before - 1 := by omega
  have hzero₀ : (lo : ℤ) - s.before < 0 → lo - s.before = 0 := by omega
  have hcast₀ : ¬ (lo : ℤ) - s.before < 0 → ((lo - s.before : ℕ) : ℤ) = (lo : ℤ) - s.before := by
    omega
  simp only [needStmt, scanFrame]
  -- The tests of the program tell four cases apart: whether the digit is an 8, and whether the
  -- difference that is then formed is negative.  In each case the block is run (first goal:
  -- everything is in range; second goal: the last state is the one stated).
  have hcases : (dg = 8 ∧ (lo : ℤ) - s.before - 1 < 0) ∨ (dg = 8 ∧ ¬ (lo : ℤ) - s.before - 1 < 0) ∨
      (dg ≠ 8 ∧ (lo : ℤ) - s.before < 0) ∨ (dg ≠ 8 ∧ ¬ (lo : ℤ) - s.before < 0) := by omega
  rcases hcases with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨h₁, h⟩ | ⟨h₁, h⟩ <;> constructor <;>
    simp [Limits.Addr, abs_le, update_frame_setLocal, *] <;>
    omega

/-- The string with the digits before p kept, the digit at p raised and the least filling behind it
is `Spec.raiseAt`. -/
theorem segN_raiseAt {μ μ' : ℕ → ℤ} {a lo p c : ℕ} {l : List ℕ} (hseg : SegN μ a l)
    (hp : p < l.length) (hkeep : ∀ b < a + p, μ' b = μ b)
    (hdigit : μ' (a + p) = (l.getD p 0 + 1 : ℕ))
    (htail : SegN μ' (a + (p + 1))
      (nineFirst (l.length - (p + 1)) (lo - c - if l.getD p 0 = 8 then 1 else 0))) :
    SegN μ' a (raiseAt lo p c l) := by
  have hlen : a + (List.map (fun x : ℕ => (x : ℤ)) (l.take p)).length = a + p := by
    rw [List.length_map, List.length_take, min_eq_left hp.le]
  rw [raiseAt, SegN, List.map_append, seg_append, List.map_cons, seg_cons, hlen, Nat.sub_sub,
    List.map_take]
  exact ⟨(hseg.take p).congr fun i hi => hkeep _ (by simp at hi; omega), hdigit, htail⟩

/-- The second pass: raise the digit at the position found, and write the least admissible filling
behind it. -/
def raiseStmt : Stmt :=
  needStmt ;;
  .store (v Str +' v Best) (v Digit +' k 1) ;;
  .set Pos (v Best +' k 1) ;;
  fillTail ;;
  .set Result (k 1)

/-- The second pass writes `Spec.raiseAt` for the position that the scan has found, and
returns 1. -/
theorem raiseStmt_spec (hs : Std lim) {μ : ℕ → ℤ} {a lo hi dg' : ℕ} {l : List ℕ}
    (hseg : SegN μ a l) (ha : a + l.length < lim.space) (hlo : lo ≤ l.count 9)
    (hfound : (nineScan hi l l.length).found = 1) :
    Ends lim P d raiseStmt ⟨scanFrame a l.length lo hi l.length (nineScan hi l l.length) dg', μ⟩
      (15 * l.length + 46) fun σ' =>
        SegN σ'.mem a
          (raiseAt lo (nineScan hi l l.length).pos (nineScan hi l l.length).before l) ∧
        σ'.loc 0 = 1 ∧ SameOutside μ σ'.mem a l.length := by
  light_facts hs
  have hinv := nineScan_inv hi l le_rfl
  generalize nineScan hi l l.length = s at hinv hfound ⊢
  have hp := hinv.pos_lt hfound
  have hdigit_le := le_of_canRaise (hinv.canRaise hfound)
  have hfits := raise_fits hp hdigit_le hlo
  rw [← hinv.before hfound] at hfits
  have hbefore : s.before ≤ l.length := by
    rw [hinv.before hfound]
    exact List.count_le_length.trans (List.length_take_le' _ _)
  have hlon : lo ≤ l.length := hlo.trans List.count_le_length
  have := needStmt_cost
  obtain ⟨dg, hdg⟩ : ∃ dg, l.getD s.pos 0 = dg := ⟨_, rfl⟩
  obtain ⟨need, hneed⟩ : ∃ need, lo - s.before - (if dg = 8 then 1 else 0) = need := ⟨_, rfl⟩
  have : need ≤ lo - s.before := hneed ▸ Nat.sub_le _ _
  rw [hdg] at hdigit_le
  -- digit := mem[str + best]; need := max (lo - before - [digit = 8]) 0
  refine Ends.next _ (Ends.block
    ((needStmt_runs hs ha hp (hdg ▸ hseg.read hp) hlon hbefore).mono ?_) le_rfl)
  rintro _ rfl
  rw [hneed]
  -- mem[str + best] := digit + 1
  light_store (a + s.pos) (dg + 1 : ℕ)
  -- pos := best + 1
  light_set (s.pos + 1 : ℕ)
  -- fillTail
  light_piece (fillTail_spec hs (i₀ := s.pos + 1) (need := need) ha (by omega) _ rfl rfl rfl
    rfl) with ⟨_, μ'⟩ ⟨rfl, htail, hsame⟩
  -- return 1
  refine Ends.setLast ⟨segN_raiseAt hseg hp (fun b hb => ?_) ?_ (by rw [hdg, hneed]; exact htail),
    by simp, ?_⟩
  · rw [hsame b (Or.inl (by omega)), Function.update_of_ne (by omega)]
  · rw [hsame _ (Or.inl (by omega)), Function.update_self, hdg]
  · exact (SameOutside.refl.update ⟨by omega, by omega⟩ _).trans (hsame.mono (by omega) (by omega))

/-! ## The routine -/

/-- nineNext(str, len, minNines, maxNines): scan the string; if a position can be raised, write the
next string and return 1, and return 0 if not.  The locals of the scan start at 0. -/
def nineNextBody : Stmt :=
  .set Pos (k 0) ;;
  .while (v Pos <' v Len) scanRound ;;
  .ite (v Found =' k 1) raiseStmt (.set Result (k 0))

/-- **nineNext** replaces the string by the next one and returns 1, or leaves the last string and
returns 0. -/
theorem nineNext_spec (hP : P[Proc.nineNext]? = some nineNextBody) (hs : Std lim) :
    NineNextSpec lim P := by
  rintro a _ lo hi l μ hseg hmem ha
  obtain ⟨rfl, -, hlo, -⟩ := (mem_nineStrs l).1 hmem
  refine fun d _ => ⟨nineNextBody, hP, ?_⟩
  light_facts hs
  unfold tNineNext
  -- pos := 0
  light_set (0 : ℕ)
  -- while pos < len
  refine Ends.next _ (Ends.whileBlock (ScanInv a lo hi l μ) l.length ?start ?round ?done
    (hT := le_rfl)) (by simp [scanRound_cost]; omega)
  case start => exact ⟨0, congrArg (State.mk · μ) (frame_append_zeros _ 5).symm⟩
  case round =>
    rintro i _ hi' ⟨dg', rfl⟩
    have hnines : (nineScan hi l i).nines ≤ i := by
      rw [(nineScan_inv hi l hi'.le).nines]
      exact List.count_le_length.trans (List.length_take_le _ _)
    exact ⟨by simp, by simp [scanFrame]; omega,
      (scanRound_runs hs ha hi' (hseg.read hi') hnines).mono fun σ' hσ' =>
        ⟨l.getD i 0, by rw [hσ', nineScan_succ hi l hi']⟩⟩
  case done =>
    rintro _ ⟨dg', rfl⟩
    refine ⟨by simp, by simp [scanFrame], ?_⟩
    simp only [scanRound_cost]
    rw [nineNext_eq_scan]
    -- if found = 1
    refine Ends.iteLast (fun hfound => ?_) (fun hfound => ?_) (by simp; omega)
    · have hfound' : (nineScan hi l l.length).found = 1 := by
        simpa [scanFrame] using hfound
      simp only [if_pos hfound', Option.getD_some, Option.isSome_some, if_true]
      exact (raiseStmt_spec hs hseg ha hlo hfound').mono (by light_time) fun _ h => h
    · have hfound' : ¬ (nineScan hi l l.length).found = 1 := by
        simpa [scanFrame] using hfound
      simp only [if_neg hfound', Option.getD_none, Option.isSome_none]
      -- return 0
      exact Ends.setLast ⟨hseg, by simp, SameOutside.refl⟩

end Light.Sec4

