/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Programs.Sec2.Theorem5.Instance

/-!
# The wanted entries of a thin matrix product, as inner products

X is an N × D matrix at the address x and Y a D × N matrix at y, both row by row, with entries of
absolute value at most U; the cells from wi and from wj on hold the rows and the columns of w wanted
positions.  thinBrute(N, D, w, U, x, y, wi, wj, out, fr) computes every wanted entry (XY)[I, J] as
the inner product of row I of X and column J of Y, and writes it to the cells from out on.  It is
right on every instance for which D U² fits in a word, so that no partial sum overflows; it is what
the solver of Theorem 5 falls back to outside the regime of the theorem.  At most
40 (w + 1) (D + 1) steps.

bruteInner_spec treats the inner product: after t rounds the sum holds the first t terms
(brutePartial), which stay within a word (abs_brutePartial_le).  bruteRound_spec treats one wanted
position, and thinBrute_spec the loop over the positions.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}


/-- The inner product. -/
def bruteInner : Stmt :=
  .while (v 11 <' v 1) (
    .set 14 (v 14 +' M (v 12) *' M (v 13)) ;;
    .set 12 (v 12 +' k 1) ;;
    .set 13 (v 13 +' v 0) ;;
    .set 11 (v 11 +' k 1))

/-- One wanted position: the inner product, the store, and the step to the next position. -/
def bruteRound :=
  .set 11 (k 0) ;;
  .set 12 (v 4 +' M (v 6 +' v 10) *' v 1) ;;
  .set 13 (v 5 +' M (v 7 +' v 10)) ;;
  .set 14 (k 0) ;;
  bruteInner ;;
  .store (v 8 +' v 10) (v 14) ;;
  .set 10 (v 10 +' k 1)

/-- thinBrute(N, D, w, U, x, y, wi, wj, out, fr). -/
def thinBruteBody : Stmt :=
  .while (v 10 <' v 2) bruteRound

/-- The locals of thinBrute: the arguments, the number i of the position, the index t, the two
addresses px and py, and the sum s.  In the place of U stands whatever number u has been passed: the
program never reads it. -/
def bruteLocs (x : ThinInst) (u : ℤ) (fr i t px py : ℕ) (s : ℤ) : List ℤ :=
  [x.N, x.D, x.w, u, x.x, x.y, x.wi, x.wj, x.out,
    fr, i, t, px, py, s]

/-! ## The partial sums -/

/-- The first n terms of the inner product. -/
def brutePartial N D (X Y : List ℤ) I J n :=
  ((List.range n).map fun t => X.getD (I * D + t) 0 * Y.getD (t * N + J) 0).sum

/-- One more term. -/
theorem brutePartial_succ N D X Y I J n :
    brutePartial N D X Y I J (n + 1)
      = brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0 := by
  simp [brutePartial, List.range_succ]

/-- A term of the inner product is at most U². -/
theorem abs_bruteTerm_le {X Y} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U) a b :
    |X.getD a 0 * Y.getD b 0| ≤ U * U := by
  rw [abs_mul]
  exact mul_le_mul (hX.abs_getD_le (by positivity) a) (hY.abs_getD_le (by positivity) b)
    (abs_nonneg _) (by positivity)

/-- The first n terms add up to at most n U². -/
theorem abs_brutePartial_le {N D} {X Y} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U)
     I J n : |brutePartial N D X Y I J n| ≤ n * (U * U) := by
  induction n with
  | zero => simp [brutePartial]
  | succ n ih =>
    rw [brutePartial_succ]
    calc |brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0|
        ≤ |brutePartial N D X Y I J n| + |X.getD (I * D + n) 0 * Y.getD (n * N + J) 0| :=
          abs_add_le _ _
      _ ≤ n * (U * U) + U * U := add_le_add ih (abs_bruteTerm_le hX hY _ _)
      _ = ((n + 1 : ℕ) : ℤ) * (U * U) := by push_cast; ring

/-! ## The program -/

variable (std : Std lim)

include std in
/-- **The inner product** of row I of X and column J of Y. -/
theorem bruteInner_spec  x {μ} {fr i I J} {u}
    (segX : Seg μ x.x x.X) (segY : Seg μ x.y x.Y) (lX : x.X.length = x.N * x.D)
    (lY : x.Y.length = x.D * x.N) (bX : AbsLe x.X x.U) (bY : AbsLe x.Y x.U) (hI : I < x.N)
    (hJ : J < x.N) (roomX : x.x + x.N * x.D < lim.space) (roomY : x.y + x.D * x.N + x.N < lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d bruteInner ⟨frame (bruteLocs x u fr i 0 (x.x + I * x.D) (x.y + J) 0), μ⟩
      (24 * x.D + 4) fun σ' => σ' = ⟨frame (bruteLocs x u fr i x.D (x.x + I * x.D + x.D)
        (x.y + x.D * x.N + J) (brutePartial x.N x.D x.X x.Y I J x.D)), μ⟩ := by


  have  := Nat.mul_add_le_mul hI (le_refl x.D)
  unfold bruteInner
  refine Ends.whileBlock (fun t σ => σ = ⟨frame (bruteLocs x u fr i t (x.x + I * x.D + t)
    (x.y + t * x.N + J) (brutePartial x.N x.D x.X x.Y I J t)), μ⟩) x.D
    (by simp [brutePartial]) ?round ?done
  case round =>
    rintro t _ ht rfl
    have  := Nat.mul_add_le_mul ht (le_refl x.N)
    have rX : μ (x.x + I * x.D + t) = x.X.getD (I * x.D + t) 0 := by
      rw [Nat.add_assoc]
      exact segX.getD (by omega) 0
    have rY : μ (x.y + t * x.N + J) = x.Y.getD (t * x.N + J) 0 := by
      rw [Nat.add_assoc]
      exact segY.getD (by omega) 0
    have hmono : ∀ n ≤ x.D, (n : ℤ) * (x.U * x.U) ≤ lim.word := fun n hn =>
      le_trans (mod_cast Nat.mul_le_mul_right (x.U * x.U) hn) hword
    have hsum := abs_le.mp ((abs_brutePartial_le (N := x.N) (D := x.D) bX bY I J (t + 1)).trans
      (mod_cast hmono (t + 1) (by omega)))
    have  := abs_le.mp ((abs_bruteTerm_le bX bY (I * x.D + t) (t * x.N + J)).trans
      (by simpa using hmono 1 (by omega)))
    have hnext := brutePartial_succ x.N x.D x.X x.Y I J t
    rw [hnext] at hsum
    generalize x.X.getD (I * x.D + t) 0 = a, x.Y.getD (t * x.N + J) 0 = b at *
    generalize hpx : x.x + I * x.D + t = px at *
    generalize hpy : x.y + t * x.N + J = py at *


    exact ⟨by simp, by simp [bruteLocs]; omega,
      by light_side [bruteLocs, rX, rY],
      by simp [bruteLocs, update_frame_setLocal, rX, rY, hnext, (by rw [← hpx]; push_cast; ring : (px : ℤ) + 1 = x.x + I * x.D + (t + 1)), (by rw [← hpy]; push_cast; ring : (py : ℤ) + x.N = x.y + (t + 1) * x.N + J)]⟩
  case done =>
    aesop

/-- Before position i: the locals are as in bruteLocs, with anything in the scratch locals, the
entries of the positions before i are in the output, and nothing else has changed. -/
def BruteInv x μ u fr i (σ : State) :=
  ∃ (t px py : ℕ) (s : ℤ) (μ' : Light.Memory), σ = ⟨frame (bruteLocs x u fr i t px py s), μ'⟩
    ∧ (∀ j < i, μ' (x.out + j) = thinEntry x.N x.D x.X x.Y (thinI x j) (thinJ x j))
    ∧ SameOutside μ μ' x.out x.w

include std in
/-- **One wanted position.** -/
theorem bruteRound_spec  {x} {μ} {fr} {u}
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) {i} (hi : i < x.w) {σ}
    (h : BruteInv x μ u fr i σ) :
    Ends lim P d bruteRound σ (24 * x.D + 33) (BruteInv x μ u fr (i + 1)) := by
  obtain ⟨t, px, py, s, μ', rfl, hdone, hfr⟩ := h


  have  := And.intro hpre.belowX (And.intro hpre.belowY (And.intro hpre.belowWI
    (And.intro hpre.belowWJ hpre.belowOut)))
  have hI := thinI_lt hpre hi
  have hJ := thinJ_lt hpre hi
  have segX  :=
    hpre.segX.of_sameOutside hfr (by ram_arith)
  have segY  :=
    hpre.segY.of_sameOutside hfr (by ram_arith)
  have rI : μ' (x.wi + i) = thinI x i := by
    rw [hfr _ (by ram_arith)]
    exact mem_thinI hpre hi
  have rJ : μ' (x.wj + i) = thinJ x i := by
    rw [hfr _ (by ram_arith)]
    exact mem_thinJ hpre hi
  have  := Nat.mul_add_le_mul hI (le_refl x.D)

  unfold bruteRound bruteLocs
  -- t := 0; px := x + mem[wi + i] * D; py := y + mem[wj + i]; s := 0
  light_set 0
  light_set (x.x + thinI x i * x.D : ℕ) using rI
  light_set (x.y + thinJ x i : ℕ) using rJ
  light_set 0
  -- the inner product
  refine Ends.next (24 * x.D + 4) ((bruteInner_spec std x (i := i) segX segY hpre.lenX hpre.lenY
    hpre.leX hpre.leY hI hJ (by omega) (by omega) hword).mono le_rfl ?_)
  rintro _ rfl
  unfold bruteLocs
  -- mem[out + i] := s; i := i + 1
  light_store (x.out + i) (brutePartial x.N x.D x.X x.Y (thinI x i) (thinJ x i) x.D)
  light_set (i + 1 : ℕ)
  refine ⟨_, _, _, _, _, rfl, fun j hj => ?_,
    hfr.update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
  · grind
  · aesop

include std in
/-- **The brute force is right on every instance** for which D U² fits in a word.  It needs N + 1
cells above the free pointer only as room for addresses that are formed and never used. -/
theorem thinBrute_spec  x μ fr u
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d thinBruteBody
      ⟨frame [x.N, x.D, x.w, u, x.x, x.y, x.wi, x.wj,
        x.out, fr], μ⟩
      (40 * ((x.w + 1) * (x.D + 1))) fun σ' => thinTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  unfold thinBruteBody
  refine Ends.whileConst (BruteInv x μ u fr) x.w (24 * x.D + 33) ?start ?round ?done ?time
  case start =>
    exact ⟨0, 0, 0, 0, μ, by rw [← frame_append_zeros _ 5]; rfl, fun j hj => absurd hj (by omega),
      SameOutside.refl⟩
  case round =>
    intro i σ hi h
    refine ⟨?_, ?_, bruteRound_spec std hpre hsp hword hi h⟩ <;>
      obtain ⟨t, px, py, s, μ', rfl, -, -⟩ := h
    · simp
    · simpa [bruteLocs] using hi
  case done =>
    rintro _ ⟨t, px, py, s, μ', rfl, hdone, hfr⟩
    refine ⟨by simp, by simp [bruteLocs], fun i hi => ?_, fun a ha => hfr a ha.2⟩
    have hi' := by rwa [length_thinOut hpre] at hi
    change μ' (x.out + i) = _
    rw [hdone i hi', ← getD_thinOut hpre hi', List.getD_eq_getElem _ _ hi]
  case time =>
    ram_grind

end Light.Sec2
