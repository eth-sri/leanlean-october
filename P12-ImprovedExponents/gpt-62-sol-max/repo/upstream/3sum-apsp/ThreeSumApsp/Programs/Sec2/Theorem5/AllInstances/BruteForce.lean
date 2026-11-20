/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.WhileShape
import ThreeSumApsp.Lang.Lib.Pass

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

In `thinBrute_spec`, the outer loop writes the prefix of answers, and the inner loop
accumulates the partial inner product `brutePartial`, bounded by `abs_brutePartial_le`.
-/

@[expose] public section

namespace Light.Sec2

open ThreeSumApsp

variable {lim : Limits} {P : Program} {d : ℕ}

namespace Brute

/-- Local 10 of thinBrute: the number of the position. -/
registers from 10 [
  Pos,
  /- Local 11 of thinBrute: the index t of the inner product. -/ Idx,
  /- Local 12 of thinBrute: the address of X[I, t]. -/ CellX,
  /- Local 13 of thinBrute: the address of Y[t, J]. -/ CellY,
  /- Local 14 of thinBrute: the sum. -/ Sum]

end Brute

open ThinArg Brute

/-- The inner product. -/
def bruteInner : Stmt :=
  .while (v Idx <' v Cols) (
    .set Sum (v Sum +' M (v CellX) *' M (v CellY)) ;;
    .set CellX (v CellX +' k 1) ;;
    .set CellY (v CellY +' v Rows) ;;
    .set Idx (v Idx +' k 1))

/-- One wanted position: the inner product, the store, and the step to the next position. -/
def bruteRound : Stmt :=
  .set Idx (k 0) ;;
  .set CellX (v AdrX +' M (v AdrWI +' v Pos) *' v Cols) ;;
  .set CellY (v AdrY +' M (v AdrWJ +' v Pos)) ;;
  .set Sum (k 0) ;;
  bruteInner ;;
  .store (v AdrOut +' v Pos) (v Sum) ;;
  .set Pos (v Pos +' k 1)

/-- thinBrute(N, D, w, U, x, y, wi, wj, out, fr). -/
def thinBruteBody : Stmt :=
  .while (v Pos <' v Wanted) bruteRound

/-- The locals of thinBrute: the arguments, the number i of the position, the index t, the two
addresses px and py, and the sum s.  In the place of U stands whatever number u has been passed: the
program never reads it. -/
def bruteLocs (x : ThinInst) (u : ℤ) (fr i t px py : ℕ) (s : ℤ) : List ℤ :=
  [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), u, (x.x : ℤ), (x.y : ℤ), (x.wi : ℤ), (x.wj : ℤ), (x.out : ℤ),
    (fr : ℤ), (i : ℤ), (t : ℤ), (px : ℤ), (py : ℤ), s]

/-! ## The partial sums -/

/-- The first n terms of the inner product. -/
def brutePartial (N D : ℕ) (X Y : List ℤ) (I J n : ℕ) : ℤ :=
  ((List.range n).map fun t => X.getD (I * D + t) 0 * Y.getD (t * N + J) 0).sum

/-- One more term. -/
theorem brutePartial_succ (N D : ℕ) (X Y : List ℤ) (I J n : ℕ) :
    brutePartial N D X Y I J (n + 1)
      = brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0 := by
  simp [brutePartial, List.range_succ]

/-- A term of the inner product is at most U². -/
theorem abs_bruteTerm_le {X Y : List ℤ} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U) (a b : ℕ) :
    |X.getD a 0 * Y.getD b 0| ≤ (U * U : ℕ) := by
  rw [abs_mul]
  push_cast
  exact mul_le_mul (hX.abs_getD_le (by positivity) a) (hY.abs_getD_le (by positivity) b)
    (abs_nonneg _) (by positivity)

/-- The first n terms add up to at most n U². -/
theorem abs_brutePartial_le {N D : ℕ} {X Y : List ℤ} {U : ℕ} (hX : AbsLe X U) (hY : AbsLe Y U)
    (I J n : ℕ) : |brutePartial N D X Y I J n| ≤ n * (U * U : ℕ) := by
  induction n with
  | zero => positivity
  | succ n ih =>
    rw [brutePartial_succ]
    calc |brutePartial N D X Y I J n + X.getD (I * D + n) 0 * Y.getD (n * N + J) 0|
        ≤ |brutePartial N D X Y I J n| + |X.getD (I * D + n) 0 * Y.getD (n * N + J) 0| :=
          abs_add_le _ _
      _ ≤ n * (U * U : ℕ) + (U * U : ℕ) := add_le_add ih (abs_bruteTerm_le hX hY _ _)
      _ = ((n + 1 : ℕ) : ℤ) * (U * U : ℕ) := by lia

/-! ## The program -/

/-- **The brute force is right on every instance** for which D U² fits in a word.  It needs N + 1
cells above the free pointer only as room for addresses that are formed and never used. -/
theorem thinBrute_spec (std : Std lim) (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) (u : ℤ)
    (hpre : x.Pre μ fr) (hsp : fr + x.N + 1 ≤ lim.space)
    (hword : ((x.D * (x.U * x.U) : ℕ) : ℤ) ≤ lim.word) :
    Ends lim P d thinBruteBody
      ⟨frame [(x.N : ℤ), (x.D : ℤ), (x.w : ℤ), u, (x.x : ℤ), (x.y : ℤ), (x.wi : ℤ), (x.wj : ℤ),
        (x.out : ℤ), (fr : ℤ)], μ⟩
      (40 * ((x.w + 1) * (x.D + 1))) fun σ' => thinTask.Post x μ fr (σ'.loc 0) σ'.mem := by
  light_facts std
  let f i := thinEntry x.N x.D x.X x.Y (thinI x i) (thinJ x i)
  unfold thinBruteBody
  refine Ends.whileShape (fun i (z : ℕ × ℕ × ℕ × ℤ) ν =>
    ⟨frame (bruteLocs x u fr i z.1 z.2.1 z.2.2.1 z.2.2.2), ν⟩)
    (fun i _ ν => ν = wrote μ x.out f i) x.w (24 * x.D + 33) (0, 0, 0, 0) μ
    wrote_zero.symm ?_ ?_
    (first := by rw [← frame_append_zeros _ 5]; rfl)
    (step := by intros; light_side [bruteLocs])
    (stop := by intros; light_side [bruteLocs]) (hT := by simp; ring_nf; omega)
  · rintro i ⟨t, px, py, sum⟩ ν hi hν
    have hfr : SameOutside μ ν x.out x.w := hν ▸ sameOutside_wrote hi.le
    have := hpre.belowX
    have := hpre.belowY
    have := hpre.belowWI
    have := hpre.belowWJ
    have := hpre.belowOut
    let I := thinI x i
    let J := thinJ x i
    have hI : I < x.N := thinI_lt hpre hi
    have hJ : J < x.N := thinJ_lt hpre hi
    have segX := hpre.segX.of_sameOutside hfr (by rw [hpre.lenX]; exact hpre.apartX.symm)
    have segY := hpre.segY.of_sameOutside hfr (by rw [hpre.lenY]; exact hpre.apartY.symm)
    have rI : ν (x.wi + i) = (I : ℕ) := by
      rw [hfr _ (by rcases hpre.apartWI with h | h <;> omega)]
      exact mem_thinI hpre hi
    have rJ : ν (x.wj + i) = (J : ℕ) := by
      rw [hfr _ (by rcases hpre.apartWJ with h | h <;> omega)]
      exact mem_thinJ hpre hi
    have hID := Nat.mul_add_le_mul hI (le_refl x.D)
    unfold bruteRound bruteLocs
    light_steps using rI, rJ
    let S (t : ℕ) : State := ⟨frame (bruteLocs x u fr i t (x.x + I * x.D + t)
      (x.y + t * x.N + J) (brutePartial x.N x.D x.X x.Y I J t)), ν⟩
    unfold bruteInner
    refine Ends.pieceThen (T₁ := 24 * x.D + 4) (R := (· = S x.D))
      (Ends.whileBlock (fun t σ => σ = S t) x.D (by simp [S, bruteLocs, brutePartial]) ?_ ?_) ?_
    · rintro t _ ht rfl
      dsimp only [S]
      have := hpre.lenX
      have := hpre.lenY
      have htN := Nat.mul_add_le_mul ht (le_refl x.N)
      have rX : ν (x.x + I * x.D + t) = x.X.getD (I * x.D + t) 0 := by
        rw [Nat.add_assoc]
        exact segX.getD (by omega) 0
      have rY : ν (x.y + t * x.N + J) = x.Y.getD (t * x.N + J) 0 := by
        rw [Nat.add_assoc]
        exact segY.getD (by omega) 0
      have hmono : ∀ n ≤ x.D, ((n : ℤ) * (x.U * x.U : ℕ)) ≤ lim.word := fun n hn =>
        le_trans (by exact_mod_cast Nat.mul_le_mul_right (x.U * x.U) hn) hword
      have hsum := abs_le.mp ((abs_brutePartial_le (N := x.N) (D := x.D) hpre.leX hpre.leY I J (t + 1)).trans
        (by exact_mod_cast hmono (t + 1) (by omega)))
      have hterm := abs_le.mp ((abs_bruteTerm_le hpre.leX hpre.leY (I * x.D + t) (t * x.N + J)).trans
        (by simpa using hmono 1 (by omega)))
      have hnext := brutePartial_succ x.N x.D x.X x.Y I J t
      rw [hnext] at hsum
      generalize x.X.getD (I * x.D + t) 0 = a, x.Y.getD (t * x.N + J) 0 = b at *
      generalize hpx : x.x + I * x.D + t = px at *
      generalize hpy : x.y + t * x.N + J = py at *
      have hpx' : (px : ℤ) + 1 = x.x + I * x.D + (t + 1) := by rw [← hpx]; push_cast; ring
      have hpy' : (py : ℤ) + x.N = x.y + (t + 1) * x.N + J := by rw [← hpy]; push_cast; ring
      exact ⟨by simp, by simp [bruteLocs]; omega,
        by light_side [bruteLocs, rX, rY],
        by simp [bruteLocs, update_frame_setLocal, rX, rY, hnext, hpx', hpy']⟩
    · rintro _ rfl
      exact ⟨by light_side [S, bruteLocs], by light_side [S, bruteLocs], rfl⟩
    · rintro _ rfl
      dsimp [S, bruteLocs]
      light_steps
      refine ⟨(_, _, _, _), _, rfl, ?_⟩
      rw [← wrote_succ, ← hν]
      rfl
  · rintro ⟨t, px, py, sum⟩ ν rfl
    refine ⟨?_, fun a ha => (sameOutside_wrote le_rfl) a ha.2⟩
    refine seg_wrote (length_thinOut hpre) fun i hi => ?_
    have hi' : i < x.w := by rwa [length_thinOut hpre] at hi
    rw [← List.getD_eq_getElem _ 0 hi]
    exact getD_thinOut hpre hi'

end Light.Sec2
