/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.Pass
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Spec.Sec3.Theorem21b.RepeatedSquaring

/-!
# APSP by repeated squaring: the three passes over the matrix

For Theorem 21(b).  The host for APSP keeps the current matrix as a list of
`n²` integers, in which a large number `INF` stands for `+∞`.  This file has its three simple
passes, each with its specification (`clip_meets`, `apInit_meets`, `apOut_meets`).

* clip(len, thr, INF, src, dst) copies `len` cells from `src` to `dst` and replaces every number
  above `thr` by `INF`.
* apInit(n, INF, adj, w, A) writes the weight matrix of the graph to `A`: 0 on the diagonal, the
  weight where there is an edge, `INF` elsewhere.
* apOut(len, INF, A, out) writes two cells for each cell of `A`: (0, 0) for `INF`, and (1, x) for
  any other number `x`.

In each proof the memory after j rounds is written down (`wrote`, `zeroedDiag`), one lemma says what
a round does to the state, and the loop rule does the rest.
-/


namespace Light.Sec3

open ThreeSumApsp.Spec

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## clip -/

namespace Clip

/- The number of cells. -/
slots Len
/- The threshold. -/
slots 1 Thresh
/- The number that stands for +∞. -/
slots 2 Big
/- The address of the source. -/
slots 3 Src
/- The address of the destination. -/
slots 4 Dst
/- The counter q. -/
slots 5 Idx

end Clip

open Clip in
/-- clip(len, thr, INF, src, dst): for q < len, dst[q] := INF if src[q] > thr, and src[q]
otherwise. -/
def clipBody : Stmt :=
  .for Idx (v Len) (
    .ite (v Thresh <' M (v Src +' v Idx))
      (.store (v Dst +' v Idx) (v Big))
      (.store (v Dst +' v Idx) (M (v Src +' v Idx))))

variable {p : ℕ} {μ : ℕ → ℤ} {INF : ℤ} {L : List ℤ}

/-- **clip** writes the clipped list to dst, changes nothing else, and takes at most 23 len + 6
steps. -/
theorem clip_meets (hp : P[p]? = some clipBody) {src dst : ℕ} {thr : ℤ}
    (hL : Seg μ src L) (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src + L.length ≤ lim.space) (hdst : dst + L.length ≤ lim.space)
    (hsep : src + L.length ≤ dst ∨ dst + L.length ≤ src) :
    Meets lim P p d [L.length, thr, INF, src, dst] μ (23 * L.length + 6) fun _ μ' =>
      Seg μ' dst (L.map (clip thr INF)) ∧ SameOutside μ μ' dst L.length := by
  refine .of_body hp ?_
  apply Ends.forFrame (fun j μ' => μ' = wrote μ dst (fun i => clip thr INF (L.getD i 0)) j)
    L.length wrote_zero.symm
  ·
    intro j μ' hj hμ
    have hread : μ' (src + j) = L.getD j 0 :=
      hμ ▸ (wrote_rest).trans (by aesop)
    have hnext := hμ ▸ wrote_succ
    -- from here on x = src[j]
    generalize L.getD j 0 = x at hread hnext
    -- if Thresh < mem[Src + Idx]
    refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
    · rw [clip] at hnext
      -- mem[Dst + Idx] := Big
      light_store (dst + j) INF
      simp_all
    · have hc' : ¬ thr < x := by simp_all
      rw [clip] at hnext
      -- mem[Dst + Idx] := mem[Src + Idx]
      light_store (dst + j) x using hread
      simp_all
  ·
    rintro _ rfl
    dsimp 
    exact ⟨seg_wrote_map _ L, sameOutside_wrote le_rfl⟩

/-! ## apInit -/

namespace ApInit

/- The number n of vertices. -/
slots Verts
/- The number that stands for +∞. -/
slots 1 Big
/- The address of the adjacency matrix. -/
slots 2 AdjAt
/- The address of the weights. -/
slots 3 WtsAt
/- The address of A. -/
slots 4 Mat
/- The counter of both passes. -/
slots 5 Idx
/- n², in the first pass. -/
slots 6 Cells
/- The address of the diagonal cell, in the second pass. -/
slots 6 Diag

end ApInit

open ApInit in
/-- The round of the first pass: A[q] := w[q] if adj[q] = 1, and INF otherwise. -/
def apInitFill : Stmt :=
  .ite (M (v AdjAt +' v Idx) =' k 1) (.store (v Mat +' v Idx) (M (v WtsAt +' v Idx)))
    (.store (v Mat +' v Idx) (v Big))

open ApInit in
/-- The round of the second pass: the diagonal cell becomes 0; the next one is n + 1 cells on. -/
def apInitDiag : Stmt := .store (v Diag) (k 0) ;; .set Diag (v Diag +' v Verts +' k 1)

open ApInit in
/-- apInit(n, INF, adj, w, A): the first pass fills the n² cells of A, the second pass puts 0 on the
diagonal. -/
def apInitBody : Stmt :=
  .set Cells (v Verts *' v Verts) ;;
  .for Idx (v Cells) apInitFill ;;
  .set Diag (v Mat) ;;
  .for Idx (v Verts) apInitDiag

/-- The entry number q of the weight matrix, the diagonal apart. -/
def apInitCell (INF : ℤ) (ADJ W : List ℤ) (q : ℕ) : ℤ :=
  if ADJ.getD q 0 = 1 then W.getD q 0 else INF

/-- The memory μ after the first j diagonal cells of the matrix at A have become 0. -/
def zeroedDiag (μ : ℕ → ℤ) (A n j : ℕ) : ℕ → ℤ :=
  fun a => if ∃ i < j, a = A + i * (n + 1) then 0 else μ a

variable {n A : ℕ}


/-- What round j of the second pass writes. -/
theorem zeroedDiag_succ (j : ℕ) :
    Function.update (zeroedDiag μ A n j) (A + j * (n + 1)) 0 = zeroedDiag μ A n (j + 1) := by
  funext a
  simp only [zeroedDiag, Nat.exists_lt_succ_right, Function.update_apply]
  grind

variable {W ADJ : List ℤ}

/-- After both passes the weight matrix stands at A. -/
theorem seg_zeroedDiag_wrote :
    Seg (zeroedDiag (wrote μ A (apInitCell INF ADJ W) (n * n)) A n n) A
      (weightList n INF ADJ W) := by
  intro q hq
  have hq' : q < n * n := by grind [weightList]
  have hdiag : (∃ i < n, A + q = A + i * (n + 1)) ↔ q / n = q % n :=
    ⟨fun ⟨i, hi, h⟩ => by
      simp_all [Nat.eq_mul_succ_iff],
    fun h => ⟨q % n, Nat.mod_lt_of_lt_mul hq', congrArg _
      ((Nat.eq_mul_succ_iff (Nat.mod_lt_of_lt_mul hq')).2 ⟨h, rfl⟩)⟩⟩
  simp_all [zeroedDiag, weightList, List.getElem_map, List.getElem_range, apInitCell, wrote_done]

variable {j : ℕ}

/-- Both passes change the n² cells of A only. -/
theorem sameOutside_zeroedDiag {μ' : ℕ → ℤ} (h : SameOutside μ μ' A (n * n))
    (hj : j ≤ n) : SameOutside μ (zeroedDiag μ' A n j) A (n * n) := by
  intro a ha
  have hno : ¬ ∃ i < j, a = A + i * (n + 1) := by
    rintro ⟨i, hi, rfl⟩
    have := Nat.mul_add_lt_mul (show i < n by omega) (show i < n by omega)
    grind
  rw [zeroedDiag, if_neg hno]
  aesop

/-- The invariant of the second pass of apInit before round j; μ is the memory after the first
pass. -/
def ApInitInv (μ : ℕ → ℤ) (n adj w A : ℕ) (INF : ℤ) (j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [n, INF, adj, w, A, j, (A + j * (n + 1) : ℕ)], zeroedDiag μ A n j⟩

variable {adj w : ℕ} {x : ℤ}

/-- **One round of the first pass of apInit**, for the cells adj[j] = x and w[j] = y: the weight y
where there is an edge, and INF where there is none. -/
theorem apInitFill_spec {n nn y : ℤ}
    (hx : μ (adj + j) = x) (hy : μ (w + j) = y) (hw : (lim.space : ℤ) ≤ lim.word)
    (hplace : adj + j < lim.space ∧ w + j < lim.space ∧ A + j < lim.space := by omega) :
    Ends lim P d apInitFill ⟨frame [n, INF, adj, w, A, j, nn], μ⟩ apInitFill.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, adj, w, A, j, nn],
        Function.update μ (A + j) (if x = 1 then y else INF)⟩ := by
  unfold apInitFill
  -- if mem[AdjAt + Idx] = 1
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
  · have hc' : x = 1 := by simp_all
    rw [if_pos hc']
    -- mem[Mat + Idx] := mem[WtsAt + Idx]
    light_store (A + j) y using hy
    rfl
  · have hc' : x ≠ 1 := by simp_all
    rw [if_neg hc']
    -- mem[Mat + Idx] := Big
    light_store (A + j) INF
    rfl

variable {o : ℕ}

/-- **One round of the second pass of apInit**, for the address o of the diagonal cell.  The next
address o + n + 1 is computed also in the last round, so it has to fit. -/
theorem apInitDiag_spec {adj w A j : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (ho : o + n + 1 ≤ lim.space := by omega) :
    Ends lim P d apInitDiag ⟨frame [n, INF, adj, w, A, j, o], μ⟩ apInitDiag.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, adj, w, A, j, (o + (n + 1) : ℕ)], Function.update μ o 0⟩ := by
  unfold apInitDiag
  -- mem[Diag] := 0 ; Diag := Diag + Verts + 1
  light_store o 0
  light_set (o + (n + 1))
  rfl

/-- **apInit** writes the weight matrix to A, changes nothing else, and takes at most
23 n² + 17 n + 18 steps.  Only n² cells are written; the space 2 n² is asked for because after the
last round of the second pass the local Diag holds A + n (n + 1), which has to fit. -/
theorem apInit_meets (hp : P[p]? = some apInitBody)     (hn : 1 ≤ n) (lenADJ : ADJ.length = n * n) (lenW : W.length = n * n)
    (segADJ : Seg μ adj ADJ) (segW : Seg μ w W) (hw : (lim.space : ℤ) ≤ lim.word)
    (hadj : adj + n * n ≤ lim.space) (hwt : w + n * n ≤ lim.space)
    (hA : A + 2 * (n * n) ≤ lim.space) (sepADJ : adj + n * n ≤ A ∨ A + n * n ≤ adj)
    (sepW : w + n * n ≤ A ∨ A + n * n ≤ w) :
    Meets lim P p d [n, INF, adj, w, A] μ (23 * (n * n) + 17 * n + 18) fun _ μ' =>
      Seg μ' A (weightList n INF ADJ W) ∧ SameOutside μ μ' A (n * n) := by
  refine .of_body hp ?_
  have hnn := Nat.le_mul_of_pos_left n hn
  light_set (n * n)
  -- for Idx < Cells: the first pass
  refine Ends.next _ (Ends.forFrame (fun j μ' => μ' = wrote μ A (apInitCell INF ADJ W) j)
    (n * n) wrote_zero.symm ?_ ?_ (hT := le_rfl)) (by simp [apInitFill]; omega)
  ·
    rintro j _ hj rfl
    -- the cells adj[j] and w[j] are as at the start
    have hadjCell : wrote μ A (apInitCell INF ADJ W) j (adj + j) = ADJ.getD j 0 :=
      (wrote_rest).trans (by aesop)
    have hwtCell : wrote μ A (apInitCell INF ADJ W) j (w + j) = W.getD j 0 :=
      (wrote_rest).trans (by aesop)
    apply (apInitFill_spec hadjCell hwtCell hw).mono le_rfl
    rintro _ rfl
    exact ⟨rfl, wrote_succ⟩
  ·
    rintro _ rfl
    -- Diag := Mat
    refine Ends.setToThen A ?_ (hT := by simp [apInitFill]; omega)
    -- for Idx < Verts: the second pass
    refine Ends.for (ApInitInv (wrote μ A (apInitCell INF ADJ W) (n * n)) n adj w A INF) n
      apInitDiag.blockCost ?_ ?_ ?_ ?_ (by omega)
      (by simp [apInitFill, apInitDiag]; omega)
    ·
      rw [ApInitInv, Nat.zero_mul]
      exact congrArg (State.mk · _) (update_frame_setLocal _ _ _)
    ·
      rintro j _ hj - rfl
      have hrow := Nat.mul_add_le_mul hj (le_refl (n + 1))
      rw [n.mul_succ n] at hrow
      apply (apInitDiag_spec hw).mono le_rfl
      rintro _ rfl
      exact ⟨rfl, by simp_all [ApInitInv, update_frame_setLocal, zeroedDiag_succ, Nat.succ_mul, Nat.add_assoc]⟩
    ·
      rintro _ - rfl
      grind [seg_zeroedDiag_wrote, sameOutside_zeroedDiag, sameOutside_wrote, le_rfl]
    ·
      rintro j _ - - rfl
      simp

/-! ## apOut -/

namespace ApOut

/- The number of cells of A. -/
slots Len
/- The number that stands for +∞. -/
slots 1 Big
/- The address of A. -/
slots 2 Mat
/- The address of the output. -/
slots 3 Out
/- The counter q. -/
slots 4 Idx
/- The address out + 2q. -/
slots 5 Pos

end ApOut

open ApOut in
/-- The two cells of the output for the cell A[q]. -/
def apOutWrite : Stmt :=
  .ite (M (v Mat +' v Idx) =' v Big)
    (.store (v Pos) (k 0) ;; .store (v Pos +' k 1) (k 0))
    (.store (v Pos) (k 1) ;; .store (v Pos +' k 1) (M (v Mat +' v Idx)))

open ApOut in
/-- The round of apOut for the cell A[q]. -/
def apOutRound : Stmt := apOutWrite ;; .set Pos (v Pos +' k 2)

open ApOut in
/-- apOut(len, INF, A, out): for q < len, the cells out[2q], out[2q + 1] become 0, 0 if A[q] = INF,
and 1, A[q] otherwise. -/
def apOutBody : Stmt := .set Pos (v Out) ;; .for Idx (v Len) apOutRound

/-- Cell number c of the output: cells 2q and 2q + 1 are 0, 0 if L[q] = INF, and 1, L[q]
otherwise. -/
def apOutCell (INF : ℤ) (L : List ℤ) (c : ℕ) : ℤ :=
  if L.getD (c / 2) 0 = INF then 0 else if c % 2 = 0 then 1 else L.getD (c / 2) 0

variable {out : ℕ}

/-- What round q writes. -/
theorem wrote_apOutCell_succ (q : ℕ) :
    Function.update (Function.update (wrote μ out (apOutCell INF L) (2 * q)) (out + 2 * q)
      (if L.getD q 0 = INF then 0 else 1)) (out + 2 * q + 1)
      (if L.getD q 0 = INF then 0 else L.getD q 0) =
        wrote μ out (apOutCell INF L) (2 * (q + 1)) := by
  grind [apOutCell, one_ne_zero, wrote_succ, Nat.add_assoc]

/-- The invariant of the loop of apOut before round j. -/
def ApOutInv (μ : ℕ → ℤ) (A out : ℕ) (INF : ℤ) (L : List ℤ) (j : ℕ) (σ : State) : Prop :=
  σ = ⟨frame [L.length, INF, A, out, j, (out + 2 * j : ℕ)], wrote μ out (apOutCell INF L) (2 * j)⟩

/-- **The two stores of a round of apOut**, for the cell A[j] = x and the address o of the output.
-/
theorem apOutWrite_spec {n : ℤ} (hread : μ (A + j) = x)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hplace : A + j < lim.space ∧ o + 1 < lim.space ∧ A + j ≠ o := by omega) :
    Ends lim P d apOutWrite ⟨frame [n, INF, A, out, j, o], μ⟩ apOutWrite.blockCost fun σ' =>
      σ' = ⟨frame [n, INF, A, out, j, o], Function.update (Function.update μ o
        (if x = INF then 0 else 1)) (o + 1) (if x = INF then 0 else x)⟩ := by
  unfold apOutWrite
  -- if mem[Mat + Idx] = Big
  refine Ends.iteLast (fun hc => ?_) (fun hc => ?_) (by light_side)
  · have hc' : x = INF := by simp_all
    rw [if_pos hc', if_pos hc']
    -- mem[Pos] := 0 ; mem[Pos + 1] := 0
    light_store o 0
    light_store (o + 1) 0
    rfl
  · have hc' : x ≠ INF := by simp_all
    rw [if_neg hc', if_neg hc']
    -- mem[Pos] := 1 ; mem[Pos + 1] := mem[Mat + Idx]
    light_store o 1
    light_store (o + 1) x using Function.update_of_ne hplace.2.2, hread
    rfl

/-- **One round of apOut** writes the pair for the cell A[j] and moves Pos on by two. -/
theorem apOutRound_spec (hL : Seg μ A L)
    (hw : (lim.space : ℤ) ≤ lim.word) (hA : A + L.length ≤ lim.space)
    (hout : out + 2 * L.length ≤ lim.space) (hsep : A + L.length ≤ out ∨ out + 2 * L.length ≤ A)
    (hj : j < L.length) :
    Ends lim P d apOutRound
      ⟨frame [L.length, INF, A, out, j, (out + 2 * j : ℕ)], wrote μ out (apOutCell INF L) (2 * j)⟩
      apOutRound.blockCost fun σ' =>
        σ' = ⟨frame [L.length, INF, A, out, j, (out + 2 * (j + 1) : ℕ)],
          wrote μ out (apOutCell INF L) (2 * (j + 1))⟩ := by
  have hread : wrote μ out (apOutCell INF L) (2 * j) (A + j) = L.getD j 0 :=
    (wrote_rest).trans (by aesop)
  rw [← wrote_apOutCell_succ]
  refine Ends.next _ ((apOutWrite_spec hread hw).mono le_rfl ?_)
    (by decide)
  rintro _ rfl
  -- Pos := Pos + 2
  exact Ends.setTo _ rfl (by light_side) (by rfl)

/-- What apOut leaves from the address `out` on: for each number of the list `L` a pair of cells.
Its first cell holds 0 if the number is `INF`; otherwise the pair holds 1 and the number. -/
def PairsAt (μ' : ℕ → ℤ) (out : ℕ) (INF : ℤ) (L : List ℤ) : Prop :=
  ∀ i (hi : i < L.length), (L[i] = INF → μ' (out + 2 * i) = 0) ∧
    (L[i] ≠ INF → μ' (out + 2 * i) = 1 ∧ μ' (out + 2 * i + 1) = L[i])

/-- **apOut** writes the pairs to out, changes nothing else, and takes at most 30 len + 8 steps. -/
theorem apOut_meets (hp : P[p]? = some apOutBody)     (hL : Seg μ A L) (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : A + L.length ≤ lim.space) (hout : out + 2 * L.length ≤ lim.space)
    (hsep : A + L.length ≤ out ∨ out + 2 * L.length ≤ A) :
    Meets lim P p d [L.length, INF, A, out] μ (30 * L.length + 8) fun _ μ' =>
      PairsAt μ' out INF L ∧ SameOutside μ μ' out (2 * L.length) := by
  refine .of_body hp ?_
  light_set out
  refine Ends.for (ApOutInv μ A out INF L) L.length apOutRound.blockCost ?_ ?_ ?_ ?_
    (by omega) (by simp [apOutRound, apOutWrite]; omega)
  ·
    simp_all [ApOutInv, wrote_zero]
  ·
    rintro j _ hj - rfl
    apply (apOutRound_spec hL hw hA hout hsep hj).mono le_rfl
    rintro _ rfl
    exact ⟨rfl, by rw [update_frame_setLocal]; rfl⟩
  ·
    rintro _ - rfl
    refine ⟨fun i hi => ?_, sameOutside_wrote le_rfl⟩
    grind [wrote, apOutCell]
  ·
    rintro j _ - - rfl
    simp
