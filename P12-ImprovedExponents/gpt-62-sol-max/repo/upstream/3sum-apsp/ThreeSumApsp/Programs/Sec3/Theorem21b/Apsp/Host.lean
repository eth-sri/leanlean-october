/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers
import ThreeSumApsp.Lang.WhileShape

public import ThreeSumApsp.Lang.PolyBounded
public import ThreeSumApsp.Programs.Sec3.Theorem21b.Apsp.Passes
public import ThreeSumApsp.Programs.Tasks

/-! Repeated squaring alternates between two buffers. Missing edges receive a large finite
sentinel at initialization; no clipping is needed between products. -/

@[expose] public section

namespace Light.Sec3

open ThreeSumApsp.Spec

namespace ApspHost

registers [Verts, Bound, Adj, Wts, Out, Src, Cells, Thresh, Big, EntryBound, Dst, Free, Power, Res, Tmp]

private def swap : Stmt :=
  .set Tmp (v Src) ;; .set Src (v Dst) ;; .set Dst (v Tmp) ;; .set Power (v Power +' v Power)

private def round (pMP : ℕ) : Stmt :=
  .call pMP [v Verts, v EntryBound, v Src, v Src, v Dst, v Free] Res ;; swap

private def setup : Stmt :=
  .set Cells (v Verts *' v Verts) ;; .set Thresh (k 2 *' (v Verts *' v Bound)) ;;
  .set Big (k 8 *' (v Verts *' v Bound)) ;; .set EntryBound (k 2 *' v Verts *' v Big) ;;
  .set Dst (v Src +' v Cells) ;; .set Free (v Dst +' v Cells)

private abbrev initial (x : GraphInst) (src : ℕ) : List ℤ := [x.n, x.U, x.adj, x.w, x.out, src]
private abbrev cells (x : GraphInst) : ℕ := x.n * x.n
private abbrev cut (x : GraphInst) : ℕ := 2 * (x.n * x.U)
private abbrev locs (x : GraphInst) (fr src dst : ℕ) (pw res tmp : ℤ) : List ℤ :=
  initial x src ++ [(cells x : ℤ), (cut x : ℕ), (sentinel x.n x.U : ℕ), (apspBound x.n x.U : ℕ),
    dst, (fr + 2 * cells x : ℕ), pw, res, tmp]

private def Buffers (fr w src dst : ℕ) : Prop :=
  (src = fr ∧ dst = fr + w) ∨ (dst = fr ∧ src = fr + w)

end ApspHost

open ApspHost

private def apBody (pMP pInit pOut : ℕ) : Stmt :=
  setup ;; .call pInit [v Verts, v Big, v Adj, v Wts, v Src] Res ;;
  .set Power (k 1) ;; .while (v Power <' v Verts) (round pMP) ;;
  .call pOut [v Cells, v Thresh, v Src, v Out] Res

def apTime (T : ℕ → ℕ → ℕ) (n U : ℕ) : ℕ :=
  Nat.clog 2 n * (T n (apspBound n U) + 32) + 90 * (n * n) + 100

def apNeed (r : ℕ → ℕ → Need) (n U : ℕ) : Need :=
  ⟨max (r n (apspBound n U)).word (apspBound n U),
    2 * (n * n) + (r n (apspBound n U)).cells, (r n (apspBound n U)).depth + 1⟩

namespace ApspHost

variable {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need} {P R : Program} {pMP pInit pOut : ℕ}
  {lim : Limits} {d fr : ℕ} {x : GraphInst} {μ : ℕ → ℤ}

private structure Ctx (P R : Program) (pMP pInit pOut : ℕ) (T : ℕ → ℕ → ℕ) (r : ℕ → ℕ → Need)
    (lim : Limits) (d : ℕ) (x : GraphInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  sol : Solves mpTask P pMP T r
  init : (P ++ R)[pInit]? = some apInitBody
  out : (P ++ R)[pOut]? = some apOutBody
  pre : x.Pre μ fr
  ok : (apNeed r x.n x.U).Ok lim fr d

private theorem Ctx.aux (C : Ctx P R pMP pInit pOut T r lim d x μ fr) :
    (r x.n (apspBound x.n x.U)).Ok lim (fr + 2 * cells x) (d + 1) :=
  C.ok.mono (le_max_left ..) (by simp [apNeed, cells]; omega) (by simp [apNeed]; omega)

private theorem Ctx.bounds (C : Ctx P R pMP pInit pOut T r lim d x μ fr) :
    (lim.space : ℤ) ≤ lim.word ∧ fr + 2 * cells x ≤ lim.space ∧ d < lim.depth ∧
      (apspBound x.n x.U : ℕ) ≤ lim.word :=
  ⟨C.ok.space, by have h := C.aux.cells; omega, by have h := C.aux.depth; omega,
    (Nat.cast_le.2 (le_max_right ..)).trans C.ok.word⟩

private theorem answer_correct (hpre : x.Pre μ fr) {ν : ℕ → ℤ} {res : ℤ}
    (h : PairsAt ν x.out (cut x) (squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n)))
    (hk : KeptBut μ ν fr x.out (2 * cells x)) : apTask.Post x μ fr res ν := by
  obtain ⟨dist, hdist, he⟩ := squareList_distances hpre.U_pos hpre.leW hpre.noNegativeCycle
  refine ⟨⟨dist, hdist, fun i j => ?_⟩, hk⟩
  have hq : i.val * x.n + j.val < (squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n)).length :=
    length_squareList _ _ _ _ _ ▸ Nat.mul_add_lt_mul i.isLt j.isLt
  obtain ⟨htop, hfin⟩ := he i j
  rw [entry, List.getD_eq_getElem _ _ hq] at htop hfin
  obtain ⟨hzero, hone⟩ := h _ hq
  simp_all

private theorem body_spec (C : Ctx P R pMP pInit pOut T r lim d x μ fr) :
    Ends lim (P ++ R) d (apBody pMP pInit pOut) ⟨frame (apTask.args x ++ [(fr : ℤ)]), μ⟩
      (apTime T x.n x.U) fun σ => apTask.Post x μ fr (σ.loc 0) σ.mem := by
  obtain ⟨hs, hf, hd, hw⟩ := C.bounds
  dsimp only [cells] at hf
  have hn := C.pre.n_pos
  have hu := C.pre.U_pos
  have ha := C.pre.belowADJ
  have hb := C.pre.belowW
  have hn₂ : x.n ≤ x.n ^ 2 := by nlinarith
  have hB : 2 * x.n ≤ apspBound x.n x.U := Nat.le_mul_of_pos_right _ (by positivity)
  have hI : sentinel x.n x.U ≤ apspBound x.n x.U := Nat.le_mul_of_pos_left _ (by omega)
  have hC : cut x ≤ sentinel x.n x.U := by dsimp [cut, sentinel]; omega
  have hI' : (sentinel x.n x.U : ℕ) ≤ lim.word := (Nat.cast_le.2 hI).trans hw
  have hB' : (2 : ℤ) * x.n ≤ lim.word := by exact_mod_cast (Nat.cast_le.2 hB).trans hw
  have hC' : (cut x : ℕ) ≤ lim.word := (Nat.cast_le.2 hC).trans hI'
  have hU' : (1 : ℤ) ≤ x.n * x.U := by exact_mod_cast Nat.mul_pos hn hu
  push_cast at hI' hC' hw
  have hB₀ : (0 : ℤ) ≤ 2 * x.n * (8 * ((x.n : ℤ) * x.U)) := by positivity
  change Ends lim (P ++ R) d (apBody pMP pInit pOut) ⟨frame (initial x fr), μ⟩ _ _
  unfold apBody apTime setup
  light_step using initial, cells
  light_step
  light_step
  light_set (apspBound x.n x.U : ℕ) using apspBound, sentinel
  light_set ((fr + cells x : ℕ) : ℤ) using initial, cells, Nat.cast_add, Nat.cast_mul
  light_set ((fr + 2 * cells x : ℕ) : ℤ) using initial, cells, Nat.cast_add, Nat.cast_mul
  light_call (apInit_meets C.init (INF := sentinel x.n x.U) (A := fr) hn C.pre.lenADJ C.pre.lenW
    C.pre.segADJ C.pre.segW hs (by omega) (by omega) (by omega) (Or.inl ha) (Or.inl hb))
    using sentinel, cells with r₀ ν₀ ⟨hseg, hk⟩
  light_set (2 ^ 0 : ℤ)
  let S t (z : ℕ × ℕ × ℤ × ℤ) ν : State :=
    ⟨frame (locs x fr z.1 z.2.1 (2 ^ t) z.2.2.1 z.2.2.2), ν⟩
  let I t (z : ℕ × ℕ × ℤ × ℤ) ν := Buffers fr (cells x) z.1 z.2.1 ∧
    Seg ν z.1 (squareList x.n x.U x.ADJ x.W t) ∧ Kept μ ν fr
  refine Ends.next _ (Ends.whileShape S I (Nat.clog 2 x.n) (T x.n (apspBound x.n x.U) + 28)
    (fr, fr + cells x, r₀, 0) ν₀ ⟨Or.inl ⟨rfl, rfl⟩, hseg, fun _ hb => hk _ (.inl hb)⟩
    ?_ ?_ (first := ?hfirst) (step := ?guard) (stop := ?last) (hT := le_rfl)) (by light_time [cells, apspBound])
  case hfirst =>
    simp [S, locs, initial, sentinel, apspBound, cells, cut, mul_assoc]
    ring_nf
    exact (frame_append_zeros _ 1).symm
  case guard =>
    intro j z ν hj _
    exact ⟨by simp, by simpa [S] using (show (2 : ℤ) ^ j < x.n by exact_mod_cast Nat.pow_lt_of_lt_clog hj)⟩
  case last =>
    intro z ν _
    exact ⟨by simp, by simpa [S] using (show (x.n : ℤ) ≤ 2 ^ Nat.clog 2 x.n by
      exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) x.n)⟩
  · rintro t ⟨src, dst, res, tmp⟩ ν ht ⟨hp, hseg, hk⟩
    dsimp only [S] at *
    dsimp only [Buffers, cells] at hp
    have hpow : (2 : ℤ) ^ t < x.n := by exact_mod_cast Nat.pow_lt_of_lt_clog ht
    have hpow₀ : (0 : ℤ) ≤ 2 ^ t := by positivity
    have hn₂ : x.n ≤ x.n * x.n := Nat.le_mul_of_pos_left _ C.pre.n_pos
    have hlen := length_squareList x.n x.U x.ADJ x.W t
    have hn := C.pre.n_pos
    have hu := C.pre.U_pos
    have hB : 1 ≤ apspBound x.n x.U := by
      change 0 < apspBound x.n x.U
      positivity
    have h₁ := abs_squareList_le (ADJ := x.ADJ) C.pre.leW ht.le
    let L := squareList x.n x.U x.ADJ x.W t
    let y : MatInst := ⟨x.n, apspBound x.n x.U, src, src, dst, L, L⟩
    have hpre : y.Pre ν (fr + 2 * cells x) := by
      refine ⟨hn, hB, hlen, hlen, hseg, hseg, h₁, h₁, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp only [y, cells] <;> omega
    unfold round
    light_call (C.sol.meets R y (fr + 2 * cells x) hpre C.aux) using y, mpTask, locs, apspBound, sentinel
      with r₁ ν₁ ⟨hm, hkeep⟩
    have hkeep : KeptBut ν ν₁ (fr + 2 * cells x) dst (cells x) := hkeep
    refine Ends.pieceLast (T₁ := swap.blockCost)
      (R := (· = S (t + 1) (dst, src, r₁, (src : ℤ)) ν₁)) ?_
      (fun _ h => ?_) (by light_time [swap, y, mpTask])
    · light_block using S, swap, locs, pow_succ'
    · exact ⟨(dst, src, r₁, src), ν₁, h, hp.symm, hm, hk.then hkeep fun _ hb =>
        ⟨hb, by omega, Or.inl (by omega)⟩⟩
  · rintro ⟨src, dst, res, tmp⟩ ν ⟨hp, hseg, hk⟩
    dsimp only [S]
    dsimp only [Buffers, cells] at hp
    have hlen := length_squareList x.n x.U x.ADJ x.W (Nat.clog 2 x.n)
    have hOut := C.pre.belowOut
    light_call (apOut_meets C.out (thr := cut x) (out := x.out) hseg hs (by omega) (by omega)
      (Or.inr (by omega))) using locs, hlen, cells with _ ν₁ ⟨hans, hkeep⟩
    exact answer_correct C.pre hans (hk.then hkeep fun _ hb =>
      ⟨hb.1, by simpa only [hlen] using hb.2⟩)

end ApspHost

theorem isHost_ap : IsHost mpTask apTask apTime apNeed := by
  refine ⟨fun P p T r hs => ?_, fun r hr => ?_⟩
  · let body := apBody p P.length (P.length + 1)
    refine ⟨[apInitBody, apOutBody, body], P.length + 2, body, by simp, fun R lim d x μ fr hpre hok => ?_⟩
    rw [List.append_assoc]
    exact body_spec ⟨hs, by simp, by simp, hpre, hok⟩
  · unfold apNeed apspBound sentinel
    poly_need [hr.word, hr.cells, hr.depth]

end Light.Sec3
