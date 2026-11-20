/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.HostContracts

/-!
# 3SUM from Convolution-3SUM: filling the arrays of the host

After [CH20, Theorem 5.1], `prep` builds the primes, zero counts, sorted input,
distinct values, and label digits in increasing address order. Sieve and sorting scratch
space starts beyond the arrays; the final stores publish the parameter block.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe Finset

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The program -/

namespace Prep

/-- The locals of prep.  The arguments: n, V, Λ, m, x and the base b.  Then the address of the
primes, the number m², the addresses of the count table, the sorted copy, the values, their
multiplicities, the table of digits, the three sets, the doubles and the cell that holds 0, and the
free pointer behind the arrays.  Then the number of primes, a local for results that are not read,
and the number of distinct values. -/
registers [Len, Bound, Digits, PrimeBound, Src, Base, Primes, Square, Count, Sorted, Val,
  Table, Sets, Top, NumPrimes, Unread, NumValues]

end Prep

open Prep in
/-- The addresses of the arrays. -/
def prepAddr : Stmt :=
  .set Primes (v Base +' k 6) ;;
  .set Square (v PrimeBound *' v PrimeBound) ;;
  .set Count (v Primes +' v PrimeBound) ;;
  .set Sorted (v Count +' v Square) ;;
  .set Val (v Sorted +' v Len) ;;
  .set Table (v Val +' v Len) ;;
  .set Sets (v Table +' v Len *' v Digits) ;;
  .set Top (v Sets +' k 3 *' v Len)

open Prep in
/-- The primes, and zeros in the count table. -/
def prepTables (pPrimes pFill : ℕ) : Stmt :=
  .call pPrimes [v PrimeBound, v Primes, v Top] NumPrimes ;;
  .call pFill [v Count, v Square, k 0] Unread

open Prep in
/-- The sorted copy of the input. -/
def prepSorted (pCopy pSort : ℕ) : Stmt :=
  .call pCopy [v Src, v Sorted, v Len] Unread ;;
  .call pSort [v Len, v Sorted, v Top] Unread

open Prep in
/-- The distinct values with their multiplicities, and the binary digits of their labels. -/
def prepValues (pDistinct pBits : ℕ) : Stmt :=
  .call pDistinct [v Len, v Sorted, v Val] NumValues ;;
  .call pBits [v NumValues, v Val, v Bound, v Digits, v Table, v Top] Unread

open Prep in
/-- The block of parameters, the cell that holds 0, and the result. -/
def prepTail : Stmt :=
  .store (v Base) (v Bound) ;;
  .store (v Base +' k 1) (v PrimeBound) ;;
  .store (v Base +' k 2) (v Digits) ;;
  .store (v Base +' k 3) (v NumPrimes) ;;
  .store (v Base +' k 4) (v Primes) ;;
  .store (v Base +' k 5) (v Count) ;;
  .set Len (v NumValues)

/-- prep(n, V, Λ, m, x, b), over the procedures pPrimes, pFill, pCopy, pSort, pDistinct, pBits. -/
def prepBody (pPrimes pFill pCopy pSort pDistinct pBits : ℕ) : Stmt :=
  prepAddr ;;
  prepTables pPrimes pFill ;;
  prepSorted pCopy pSort ;;
  prepValues pDistinct pBits ;;
  prepTail

/-- The arguments of prep and the addresses that prepAddr computes, as the list of the locals. -/
abbrev prepFrame (a : Map) (V x : ℕ) : List ℤ :=
  [a.n, V, a.Λ, a.m, x, a.b, a.pr, ((a.m * a.m : ℕ) : ℤ), a.cnt, a.srt, a.val, a.bt, a.A,
    a.top]

/-! ## The five parts -/

/-- prepAddr computes the addresses. -/
theorem prepAddr_runs (a : Map) (V x : ℕ) (μ : ℕ → ℤ) (htop : (a.top : ℤ) ≤ lim.word)
    (hword : (6 : ℤ) ≤ lim.word) :
    prepAddr.Runs lim ⟨frame [a.n, V, a.Λ, a.m, x, a.b], μ⟩ (· = ⟨frame (prepFrame a V x), μ⟩) := by
  have hmap := a.layout
  exact ⟨by light_side [prepAddr],
    by simp [prepAddr, update_frame_setLocal, prepFrame, Map.top, Map.A, Map.bt,
      Map.val, Map.srt, Map.cnt, Map.pr]⟩

/-- What prep may use covers what the sieve needs. -/
private theorem ok_primes {n V Λ m fr : ℕ} (h : (prepNeed n V Λ m).Ok lim fr d) :
    (primesNeed m).Ok lim fr (d + 1) := by
  have : m + 1 ≤ (m + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  refine h.mono ?_ ?_ ?_ <;> simp only [primesNeed, prepNeed] <;> omega

/-- What prep may use covers what sorting needs. -/
private theorem ok_sort {n V Λ m fr : ℕ} (h : (prepNeed n V Λ m).Ok lim fr d) :
    (sortNeed n V).Ok lim fr (d + 1) := by
  refine h.mono ?_ ?_ ?_ <;> simp only [sortNeed, prepNeed] <;> omega

/-- The labels for V have `Lam V` binary digits. -/
private theorem two_mul_lt_two_pow_Lam (V : ℕ) : 2 * V < 2 ^ Lam V :=
  Nat.lt_pow_succ_log_self (by norm_num) _

/-- `2 ^ Lam V` is at most twice as large as it has to be. -/
private theorem two_pow_Lam_le {V : ℕ} (hV : 1 ≤ V) : 2 ^ Lam V ≤ 4 * V + 4 := by
  have := Nat.pow_log_le_self 2 (x := 2 * V) (by omega)
  rw [Lam, pow_succ]
  omega

/-- The time of bits grows with the number of elements. -/
private theorem tBits_mono {len len' : ℕ} (h : len ≤ len') (Λ : ℕ) : tBits len Λ ≤ tBits len' Λ :=
  Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ h) _) _

/-- prepTail writes the parameter block and returns the number of distinct values. -/
theorem prepTail_ends (a : Map) {V x np nd : ℕ} {μ : ℕ → ℤ} (r : ℤ) (htop : a.top ≤ lim.space)
    (hw : (lim.space : ℤ) ≤ lim.word) (hword : (5 : ℤ) ≤ lim.word) :
    Ends lim P d prepTail ⟨frame (prepFrame a V x ++ [(np : ℤ), r, nd]), μ⟩ 33 fun σ' =>
      σ'.loc 0 = nd ∧ CtxAt σ'.mem a.cx V a.m a.Λ np a.pr a.cnt ∧ SameOutside μ σ'.mem a.b 6 := by
  have hmap := a.layout
  unfold prepTail
  light_steps
  refine ⟨rfl, by simp [CtxAt, seg_cons, Map.cx, Nat.add_assoc], ?_⟩
  intro c hc
  simp only [Function.update_apply]
  split_ifs <;> first | rfl | omega

/-! ## The whole routine -/

/-- The arrays of the map lie as the loop over the splittings wants them. -/
theorem FrontMem.of_map (a : Map) {μ : ℕ → ℤ} {V : ℕ} {D : List ℤ} (hle : D.length ≤ a.n)
    (hnodup : D.Nodup) (hbdd : AbsLe D V) (hval : Seg μ a.val D)
    (htable : Seg μ a.bt (bitTable V a.Λ D))
    (hctx : CtxAt μ a.cx V a.m a.Λ #(Nat.primesLE a.m) a.pr a.cnt)
    (hprimes : PrimesAt μ a.pr #(Nat.primesLE a.m) a.m) (hzero : ZeroAt μ a.cnt (a.m * a.m)) :
    FrontMem μ (a.front V D) := by
  have hmap := a.layout
  have hnp := Nat.card_primesLE_le a.m
  have hrows := Nat.mul_le_mul_right a.Λ hle
  exact ⟨rfl, hle, hnodup, fun e he => hbdd e (List.mem_toFinset.1 he),
    hval, htable, hctx, hprimes, hzero, by dsimp only [Map.front, InOrder]; omega⟩

/-- **prep** meets its specification. -/
theorem prep_spec {p pPrimes pFill pCopy pSort pDistinct pBits : ℕ}
    (hP : P[p]? = some (prepBody pPrimes pFill pCopy pSort pDistinct pBits))
    (hPr : PrimesSpec lim P pPrimes) (hFi : P[pFill]? = some fillBody)
    (hCo : P[pCopy]? = some copyBody) (hSo : SortSpec lim P pSort)
    (hDi : DistinctSpec lim P pDistinct) (hBi : BitsSpec lim P pBits) : PrepSpec lim P p := by
  intro d a V x X μ C hseg
  refine Meets.of_body hP ?_
  have hmap := a.layout
  have hw := C.ok.space
  have hcells := C.ok.cells
  have hword := C.ok.word
  have hdepth := C.ok.depth
  light_facts C
  simp only [prepNeed] at hcells hword hdepth
  push_cast at hword
  have : (0 : ℤ) ≤ ((a.m : ℤ) + 1) ^ 2 := by positivity
  have hnp := Nat.card_primesLE_le a.m
  unfold tPrep prepBody
  refine Ends.next _ (Ends.block ((prepAddr_runs a V x μ (by omega) (by omega)).mono ?_) le_rfl)
    (by simp [prepAddr])
  rintro _ rfl
  simp only [prepAddr, Stmt.blockCost, Expr.cost]
  unfold prepTables prepSorted prepValues
  light_call (hPr (d + 1) a.top a.m a.pr μ (by omega) (ok_primes C.ok))
    with _ μ₁ ⟨rfl, hprimes, keep₁⟩
  light_call (fill_meets (μ := μ₁) (dst := a.cnt) (n := a.m * a.m) (x := 0) hFi hw (by omega))
    with _ μ₂ ⟨hzero, keep₂⟩
  have hroom : a.srt + X.length ≤ lim.space := by omega
  light_call (copy_meets (μ := μ₂) (src := x) (dst := a.srt) (n := X.length) hCo hw
    (by omega) hroom (.inl (by omega))) using C.len with _ μ₃ ⟨hcopy, keep₃⟩
  have hX : Seg μ₂ x X := hseg.keep
  light_call (hSo (d + 1) a.top a.srt V X μ₃
    (fun i hi => (hcopy i hi).trans (hX i hi)) C.bounded (by omega) (C.len ▸ ok_sort C.ok))
    using C.len with _ μ₄ ⟨⟨L, hL, hperm, hsorted⟩, keep₄⟩
  simp only [C.len]
  have hlen : L.length = a.n := hperm.length_eq.trans C.len
  light_call (hDi (d + 1) a.srt a.val L μ₄
    ⟨hsorted, hL, .inl (by omega), by omega, by omega, hw, by omega⟩) using hlen
    with _ μ₅ ⟨⟨D, rfl, hDn, hDv, hD⟩, keep₅⟩
  simp only [hlen]
  have hvalues := Values.of_perm C.len hperm hDn hDv
  have hDle := hvalues.length_le
  have hrows := Nat.mul_le_mul_right a.Λ hDle
  have hDV : AbsLe D V := fun e he =>
    C.bounded e (hperm.mem_iff.1 (List.mem_toFinset.1 (hDv ▸ List.mem_toFinset.2 he)))
  have htime := tBits_mono hDle a.Λ
  have hctx : Bits.Ctx lim μ₅ a.val V a.Λ a.bt D :=
    ⟨hDV, C.digits ▸ two_mul_lt_two_pow_Lam V, C.digits ▸ two_pow_Lam_le C.bound_pos, hD,
      .inl (by omega), by omega, by omega, hw, by omega⟩
  light_call (hBi (d + 1) a.top a.val a.bt V a.Λ D μ₅ hctx) with r μ₆ ⟨hbits, keep₆⟩
  refine (prepTail_ends a r (by omega) hw (by omega)).mono (by light_time [copyTime, fillTime]) ?_
  rintro ⟨_, μ₇⟩ ⟨hres, hctx, keep₇⟩
  have hlenT := length_bitTable V a.Λ D
  have hpLen : (((Nat.primesLE a.m).sort (· ≤ ·)).map fun q : ℕ => (q : ℤ)).length ≤ a.m := by
    simpa using hnp
  have hzLen := List.length_replicate (n := a.m * a.m) (a := (0 : ℤ))
  have hz : Seg μ₇ a.cnt (List.replicate (a.m * a.m) 0) := hzero.keep
  exact ⟨⟨D, L, hres, hvalues.values, FrontMem.of_map a hDle hDn hDV hD.keep hbits.keep hctx
    ⟨rfl, hprimes.keep⟩ (fun i hi => (hz i (by simpa using hi)).trans (List.getElem_replicate ..)),
    hL.keep, hperm, hsorted⟩, by light_keep⟩

end Light.Sec3.ChanHe
