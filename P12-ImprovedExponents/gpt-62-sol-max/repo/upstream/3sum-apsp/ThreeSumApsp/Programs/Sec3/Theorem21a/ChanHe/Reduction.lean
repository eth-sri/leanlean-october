/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers
import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.HostContracts
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Round
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Repeated

/-! The Chan–He host handles distinct values via its splitting grid, and repeated values
via a two-pointer scan of the sorted input. -/

@[expose] public section

open ThreeSumApsp

namespace Light.Sec3.ChanHe

open ThreeSumApsp.ChanHe ThreeSumApsp.Spec Finset

/-- The reduction on three distinct values, with repeated values left to the scan. -/
theorem threeSum_iff_trees {n U : ℕ} (hn : 1 ≤ n) (x : Fin n → ℤ) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ThreeSum x ↔
      (∃ β < Lam (2 * U), ∃ β' < Lam (2 * U), ∃ v,
        SplitYes (mPar n (2 * U)) (Lam (2 * U)) (fuel n) (2 * U) (univ.image x) β β' v) ∨
      Degenerate x := by
  have hb : Bdd (2 * U) (univ.image x) := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := mem_image.mp hy
    exact (hx i).trans (by push_cast; omega)
  rw [threeSum_iff_distinct_or_degenerate, distinct_iff_split hb]
  refine or_congr (exists_congr fun β => and_congr_right fun _ => exists_congr fun β' =>
    and_congr_right fun _ => exists_congr fun v => ?_) Iff.rfl
  have hc := card_image_univ_le x
  exact reduction_correct_oneArray hn ⟨(card_filter_le _ _).trans hc, (card_filter_le _ _).trans hc,
    (card_filter_le _ _).trans hc, hb.mono (filter_subset _ _), hb.mono (filter_subset _ _),
    hb.mono (filter_subset _ _)⟩

/-- The steps of the routine are within the time of the host. -/
theorem ChCore.time_le (T : ℕ → ℕ → ℕ) (n V : ℕ) :
    tParams n V + tPrep n (Lam V) (mPar n V)
        + tGrid T n V (mPar n V) #(Nat.primesLE (mPar n V)) (fuel n) (Lam V)
        + tRepeated n + 110 ≤ coreTime T n V := by
  set m := mPar n V
  set np := #(Nat.primesLE m)
  set Λ := Lam V
  set tt := tTree T n V m np (fuel n) with htt
  have htree : tt = callsB n * nodeOwn n V m np + callsB n * T (8 * m ^ 2) (60 * V + 40) := by
    rw [htt, tTree, tNodes_eq, callsB]
    ring
  have hgrid : tGrid T n V m np (fuel n) Λ
      = Λ ^ 2 * (6 * tPick n + 2 * tt + 296) + 14 * Λ + 10 := by
    simp only [tGrid, tRound, ← htt]
    ring
  have hcore : coreTime T n V = tParams n V + tPrep n Λ m
      + (Λ ^ 2 * (6 * tPick n + 2 * tt + 296) + 304 * Λ ^ 2)
      + tRepeated n + 400 := by
    simp only [coreTime, coreOwn, coreCalls, inputsB, tSetup]
    rw [htree]
    ring
  have hsq : Λ ≤ Λ ^ 2 := Nat.le_self_pow two_ne_zero Λ
  rw [hgrid, hcore]
  omega

/-! ## The program -/

namespace Core

registers [Len, Bound, Src, Free, Unread, Digits, PrimeBound, Levels, Base, NumValues, Sorted,
  Val, Table, Sets, Top, AnsRepeat]

end Core

open Core in
/-- The parameters, and the arrays. -/
def coreSetup (pParams pPrep : ℕ) : Stmt :=
  .call pParams [v Len, v Bound, v Free] Unread ;;
  .set Digits (M (v Free)) ;;
  .set PrimeBound (M (v Free +' k 1)) ;;
  .set Levels (M (v Free +' k 2)) ;;
  .set Base (v Free +' k 3) ;;
  .call pPrep [v Len, v Bound, v Digits, v PrimeBound, v Src, v Base] NumValues

open Core in
/-- The addresses of the arrays from the sorted copy on. -/
def coreAddr : Stmt :=
  .set Sorted (v Base +' k 6 +' v PrimeBound +' v PrimeBound *' v PrimeBound) ;;
  .set Val (v Sorted +' v Len) ;;
  .set Table (v Val +' v Len) ;;
  .set Sets (v Table +' v Len *' v Digits) ;;
  .set Top (v Sets +' k 3 *' v Len)

open Core in
/-- Test repeated values first, and only run the splitting grid if necessary. -/
def coreBody (pParams pPrep pGrid pRepeat : ℕ) : Stmt :=
  coreSetup pParams pPrep ;; coreAddr ;; .call pRepeat [v Len, v Sorted] AnsRepeat ;;
  .ite (k 0 <' v AnsRepeat) (.set Len (k 1))
    (.call pGrid [v NumValues, v Val, v Table, v Digits, v Sets, v Len, v Levels, v Base, v Top] Len)

variable {lim : Limits} {P : Program} {d : ℕ}

open Core

/-! ## The arrays, and a three-set input in the memory -/

namespace Core

/-- The parameters are those of the reduction. -/
structure Par (a : Map) (V f : ℕ) : Prop where
  len_pos : 1 ≤ a.n
  bound_pos : 1 ≤ V
  primeBound : a.m = mPar a.n V
  digits : a.Λ = Lam V
  levels : f = fuel a.n

/-- There is a prime up to m. -/
theorem Par.primes_nonempty {a : Map} {V f : ℕ} (h : Par a V f) : (Nat.primesLE a.m).Nonempty := by
  have hcard := wPar_le_card_primesLE a.n V
  rw [← h.primeBound] at hcard
  have hpos : 1 ≤ wPar a.n V :=
    Nat.mul_pos (Nat.mul_pos (by norm_num) (Nat.succ_pos _)) (Nat.succ_pos _)
  exact Finset.card_pos.1 (by omega)

/-- The bound on the primes is positive. -/
theorem Par.primeBound_pos {a : Map} {V f : ℕ} (h : Par a V f) : 1 ≤ a.m :=
  (Finset.card_pos.2 h.primes_nonempty).trans_le (Nat.card_primesLE_le a.m)

end Core

/-- **core meets its specification.** -/
theorem core_spec {p pParams pPrep pGrid pRepeat : ℕ} {T : ℕ → ℕ → ℕ} {r : ℕ → ℕ → Need}
    (hP : P[p]? = some (coreBody pParams pPrep pGrid pRepeat))
    (hParams : ParamsSpec lim P pParams) (hPrep : PrepSpec lim P pPrep)
    (hGrid : GridSpec lim P pGrid T r) (hRep : P[pRepeat]? = some repeatedBody) :
    CoreSpec lim P p T r := by
  intro d n U x b X μ hlen hXU hseg hxb hn hU hok
  have hx : ∀ i, |vecOf n X i| ≤ (U : ℤ) := fun i => by
    have hi : i.val < X.length := by rw [hlen]; exact i.isLt
    simp only [vecOf, List.getD_eq_getElem _ _ hi]
    exact hXU.getElem hi
  have hX : AbsLe X (2 * U : ℕ) := fun y hy => (hXU y hy).trans (by push_cast; omega)
  obtain ⟨a, ha, hb, hpar⟩ : ∃ a : Map, a.n = n ∧ a.b = b + 3 ∧ Par a (2 * U) (fuel a.n) :=
    ⟨⟨b + 3, n, Lam (2 * U), mPar n (2 * U)⟩, rfl, rfl, hn, by omega, rfl, rfl, rfl⟩
  have hmap := a.layout
  refine .of_body hP ?_
  rw [← ha] at hlen hx hxb hok ⊢
  have hfinal := threeSum_iff_trees hpar.len_pos (vecOf a.n X) hx
  have ht := ChCore.time_le T a.n (2 * U)
  rw [← hpar.primeBound, ← hpar.digits] at hfinal ht
  have hspace := hok.space
  have hcells := hok.cells
  have hword := hok.word
  have hdepth := hok.depth
  simp only [coreNeed, coreCells, ← hpar.primeBound, ← hpar.digits] at hcells hword hdepth
  push_cast at hword
  have hsq : (0 : ℤ) ≤ 8 * ((a.m : ℤ) + 1) ^ 2 := by positivity
  refine Ends.mono ?_ ht fun _ h => h
  unfold coreBody coreSetup coreAddr
  light_call (hParams (d + 1) a.n (2 * U) b μ (by omega) hspace
    (by rw [← hpar.primeBound]; push_cast; omega) (by omega)) with unread μ₁ ⟨hp, same₁⟩
  rw [← hpar.primeBound, ← hpar.digits, ← hpar.levels] at hp
  have h0 : μ₁ b = a.Λ := by simpa using hp 0 (by simp)
  have h1 : μ₁ (b + 1) = a.m := by simpa using hp 1 (by simp)
  have h2 : μ₁ (b + 2) = fuel a.n := by simpa using hp 2 (by simp)
  have ha₁ : ((b : ℤ) + 1).toNat = b + 1 := by omega
  have ha₂ : ((b : ℤ) + 2).toNat = b + 2 := by omega
  light_set a.Λ using h0
  light_set a.m using ha₁, h1
  light_set (fuel a.n) using ha₂, h2
  light_set a.b using hb
  light_call (hPrep (d + 1) a (2 * U) x X μ₁
    ⟨hlen, hX, by omega, hpar.bound_pos, hpar.digits,
      ⟨by simp only [prepNeed]; push_cast; omega, by simp only [prepNeed]; omega,
        hspace, by simp only [prepNeed]; omega⟩⟩ (hseg.of_sameOutside same₁ (by omega)))
    with _ μ₂ ⟨⟨D, L, rfl, hvalues, hfront, hsegL, hperm, hsorted⟩, kept₂⟩
  light_set a.srt
  light_set a.val
  light_set a.bt
  light_set a.A
  light_set a.top
  light_call (repeated_meets hRep hlen hperm hsorted (fun y hy => hX y (hperm.mem_iff.1 hy))
    hsegL (by omega) hspace (by push_cast; omega)) with _ μ₃ ⟨rfl, rfl⟩
  rw [← hvalues] at hfinal
  have kept : Kept μ μ₃ b := by light_keep
  have htst : 0 < flag (Degenerate (vecOf a.n X)) ↔ Degenerate (vecOf a.n X) := by
    unfold flag
    split <;> simp_all
  light_if yes no : Degenerate (vecOf a.n X) using htst
  · light_set (1 : ℤ)
    exact ⟨(flag_of (hfinal.mpr (.inr yes))).symm, kept⟩
  · have hg : GridPre lim r (a.front (2 * U) D) (fuel a.n) 1 (d + 1) :=
      ⟨hpar.bound_pos, hpar.primeBound_pos, hpar.digits, hpar.primes_nonempty,
        by dsimp only [Map.front]
           exact ⟨by simp only [gridNeed]; push_cast; omega, by simp only [gridNeed]; omega,
             hspace, by simp only [gridNeed]; omega⟩⟩
    light_call (hGrid _ _ μ₃ hfront (d + 1) hg) with _ μ' ⟨rfl, keep⟩
    change KeptBut μ₃ μ' a.top a.A (3 * a.n) at keep
    exact ⟨flag_congr (by simpa [no] using hfinal.symm), by light_keep⟩

end Light.Sec3.ChanHe
