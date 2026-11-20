/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Lib.SquarePass
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Spec.Sec3.Theorem21b.RepeatedSquaring

/-! APSP initializes a weight matrix and writes the distance/availability pairs. -/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## apInit -/

namespace ApInit
registers [Verts, Big, AdjAt, WtsAt, Mat, Row, Col]

def idx : Expr := v Row *' v Verts +' v Col
def cell : Stmt :=
  .ite (v Row =' v Col) (.store (v Mat +' idx) (k 0))
    (.ite (M (v AdjAt +' idx) =' k 1) (.store (v Mat +' idx) (M (v WtsAt +' idx)))
      (.store (v Mat +' idx) (v Big)))
end ApInit

open ApInit in
def apInitBody : Stmt := squarePass Row Col cell

open ApInit in
/-- Initialize the weight matrix in one pass: diagonal zero, absent edges masked by the sentinel. -/
theorem apInit_meets {p : ℕ} (hp : P[p]? = some apInitBody) {μ : ℕ → ℤ} {n adj w A : ℕ} {INF : ℤ}
    {ADJ W : List ℤ} (hn : 1 ≤ n) (lenADJ : ADJ.length = n * n) (lenW : W.length = n * n)
    (segADJ : Seg μ adj ADJ) (segW : Seg μ w W) (hw : (lim.space : ℤ) ≤ lim.word)
    (hadj : adj + n * n ≤ lim.space) (hwt : w + n * n ≤ lim.space) (hA : A + n * n ≤ lim.space)
    (sepADJ : Apart adj (n * n) A (n * n)) (sepW : Apart w (n * n) A (n * n)) :
    Meets lim P p d [(n : ℤ), INF, adj, w, A] μ (42 * (n * n) + 14 * n + 6) fun _ μ' =>
      Seg μ' A (weightList n INF ADJ W) ∧ SameOutside μ μ' A (n * n) := by
  let L := weightList n INF ADJ W
  let f q := L.getD q 0
  have hL : L.length = n * n := by simp [L, weightList]
  have hn₂ : n ≤ n * n := Nat.le_mul_of_pos_left _ hn
  refine .of_body hp ?_
  unfold apInitBody
  have hn' : (n : ℤ) ≤ lim.word := by omega
  refine (Ends.squarePass (r := Row) (c := Col) (dst := A) (T := 42 * (n * n) + 14 * n + 6)
    f hn' rfl ?_ (hT := by light_time [cell, idx])).mono le_rfl ?_
  · intro i j hi hj
    let q := i * n + j
    have hq : q < n * n := Nat.mul_add_lt_mul hi hj
    let ν := wrote μ A f q
    have h₁ : ν (adj + q) = ADJ.getD q 0 :=
      (wrote_rest (by omega)).trans (segADJ.getD (lenADJ ▸ hq) 0)
    have h₂ : ν (w + q) = W.getD q 0 :=
      (wrote_rest (by omega)).trans (segW.getD (lenW ▸ hq) 0)
    have hv : f q = if i = j then 0 else if ADJ.getD q 0 = 1 then W.getD q 0 else INF := by
      dsimp [f, L, weightList, q]
      rw [List.getD_map_range _ hq, Nat.mul_add_div_of_lt hj, Nat.mul_add_mod_of_lt hj]
    have ha (b : ℕ) : ((b : ℤ) + ((i : ℤ) * n + j)).toNat = b + q := by
      rfl
    have hF : rectLoc (frame [n, INF, adj, w, A]) Row Col i j = frame [n, INF, adj, w, A, i, j] := by
      rw [rectLoc, update_frame_setLocal, update_frame_setLocal]
      rfl
    change Ends lim P d cell ⟨_, ν⟩ cell.blockCost (· = ⟨_, wrote μ A f (q + 1)⟩)
    rw [hF, ← wrote_succ, hv]
    have hq' : (i : ℤ) * n + j < (n : ℤ) * n := by exact_mod_cast hq
    simp only [List.getD_eq_getElem?_getD] at h₁ h₂ ⊢
    by_cases he : i = j
    · subst i
      light_block using cell, idx, ha <;> rfl
    · by_cases hb : ADJ[q]?.getD 0 = 1 <;>
        (light_block using cell, idx, ha, h₁, h₂, he, hb <;> rfl)
  · intro σ hσ
    change Seg σ.mem A L ∧ SameOutside μ σ.mem A (n * n)
    rw [hσ]
    exact ⟨seg_wrote hL fun i hi => (List.getD_eq_getElem _ _ hi).symm, sameOutside_wrote le_rfl⟩

/-! ## apOut -/

namespace ApOut

/-- The number of cells of A. -/
registers [
  Len,
  /- The number that separates finite and infinite distances. -/ Thresh,
  /- The address of A. -/ Mat,
  /- The address of the output. -/ Out,
  /- The counter q. -/ Idx,
  /- The address out + 2q. -/ Pos]

end ApOut

open ApOut in
/-- The two cells of the output for the cell A[q]. -/
def apOutWrite : Stmt :=
  .ite (v Thresh <' M (v Mat +' v Idx))
    (.store (v Pos) (k 0) ;; .store (v Pos +' k 1) (k 0))
    (.store (v Pos) (k 1) ;; .store (v Pos +' k 1) (M (v Mat +' v Idx)))

open ApOut in
/-- The round of apOut for the cell A[q]. -/
def apOutRound : Stmt := apOutWrite ;; .set Pos (v Pos +' k 2)

open ApOut in
/-- apOut(len, thr, A, out): for q < len, the cells out[2q], out[2q + 1] become 0, 0 if A[q] > thr,
and 1, A[q] otherwise. -/
def apOutBody : Stmt := .set Pos (v Out) ;; .for Idx (v Len) apOutRound

/-- Cell number c of the output: cells 2q and 2q + 1 are 0, 0 if L[q] > thr, and 1, L[q]
otherwise. -/
def apOutCell (thr : ℤ) (L : List ℤ) (c : ℕ) : ℤ :=
  if thr < L.getD (c / 2) 0 then 0 else if c % 2 = 0 then 1 else L.getD (c / 2) 0

/-- What round q writes. -/
private theorem wrote_apOutCell_succ {μ : ℕ → ℤ} {out : ℕ} {thr : ℤ} {L : List ℤ} (q : ℕ) :
    Function.update (Function.update (wrote μ out (apOutCell thr L) (2 * q)) (out + 2 * q)
      (if thr < L.getD q 0 then 0 else 1)) (out + 2 * q + 1)
      (if thr < L.getD q 0 then 0 else L.getD q 0) =
        wrote μ out (apOutCell thr L) (2 * (q + 1)) := by
  have heven : apOutCell thr L (2 * q) = if thr < L.getD q 0 then 0 else 1 := by
    light_side [apOutCell]
  have hodd : apOutCell thr L (2 * q + 1) = if thr < L.getD q 0 then 0 else L.getD q 0 := by
    simp only [apOutCell, show (2 * q + 1) / 2 = q by omega, show (2 * q + 1) % 2 = 1 by omega,
      one_ne_zero, if_false]
  rw [← heven, wrote_succ, Nat.add_assoc, ← hodd, wrote_succ]
  rfl

/-- What apOut leaves from the address `out` on: for each number of the list `L` a pair of cells.
Its first cell holds 0 if the number is above `thr`; otherwise the pair holds 1 and the number. -/
def PairsAt (μ' : ℕ → ℤ) (out : ℕ) (thr : ℤ) (L : List ℤ) : Prop :=
  ∀ i (hi : i < L.length), (thr < L[i] → μ' (out + 2 * i) = 0) ∧
    (¬ thr < L[i] → μ' (out + 2 * i) = 1 ∧ μ' (out + 2 * i + 1) = L[i])

/-- **apOut** writes the pairs to out, changes nothing else, and takes at most 30 len + 8 steps. -/
theorem apOut_meets {p : ℕ} (hp : P[p]? = some apOutBody) {μ : ℕ → ℤ} {A out : ℕ} {thr : ℤ}
    {L : List ℤ} (hL : Seg μ A L) (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : A + L.length ≤ lim.space) (hout : out + 2 * L.length ≤ lim.space)
    (hsep : A + L.length ≤ out ∨ out + 2 * L.length ≤ A) :
    Meets lim P p d [L.length, thr, A, out] μ (30 * L.length + 8) fun _ μ' =>
      PairsAt μ' out thr L ∧ SameOutside μ μ' out (2 * L.length) := by
  refine .of_body hp ?_
  unfold apOutBody
  -- Pos := Out
  light_step
  let S (j : ℕ) := (⟨frame [L.length, thr, A, out, j, (out + 2 * j : ℕ)],
    wrote μ out (apOutCell thr L) (2 * j)⟩ : State)
  refine Ends.for (fun j σ => σ = S j) L.length apOutRound.blockCost ?_ ?_ ?_
    (by rintro j _ - - rfl; exact ⟨trivial, rfl⟩) (by omega) (by light_time [apOutRound, apOutWrite])
  · simp [S, update_frame_setLocal, wrote_zero]
  · rintro j _ hj - rfl
    have hread : (S j).mem (A + j) = L.getD j 0 :=
      (wrote_rest (by omega)).trans (hL.getD hj 0)
    dsimp only [S] at hread ⊢
    rw [← wrote_apOutCell_succ]
    simp only [List.getD_eq_getElem?_getD] at hread ⊢
    by_cases h : thr < L[j]?.getD 0 <;>
      (light_block using apOutRound, apOutWrite, hread, h <;> grind)
  · rintro _ - rfl
    refine ⟨fun i hi => ?_, sameOutside_wrote le_rfl⟩
    dsimp [S]
    rw [wrote_done (by omega), Nat.add_assoc, wrote_done (by omega)]
    simp [apOutCell, show (2 * i + 1) / 2 = i by omega]
    split <;> simp_all

end Light.Sec3
