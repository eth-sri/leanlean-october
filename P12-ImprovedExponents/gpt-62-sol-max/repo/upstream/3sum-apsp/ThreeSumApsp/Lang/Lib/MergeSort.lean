/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

public import ThreeSumApsp.Lang.Lib.Copy
public import ThreeSumApsp.Lang.Lib.Logs
public import ThreeSumApsp.Lang.Lib.Merge

/-!
# Merge sort

sort(n, a, fr) sorts the n cells from a in place, in ascending order (`sort_meets`).  It is the
recursive merge sort: sort the first ⌈n/2⌉ cells, sort the rest, merge the two halves into the n
cells from the free pointer fr, and copy them back.  It calls half, merge and copy.

The proof is an induction on n. The number of steps,
`sortTime n`, is of the order n log n (`clog_split`, `time_split`), and the calls are nested
⌈log₂ n⌉ + 1 deep.  Numbers are only compared and copied, so their size does not matter.
-/

@[expose] public section

namespace Light

variable {lim : Limits} {P : Program}

namespace MergeSort

/-- The local variables of sort: the arguments n, a and fr; h = ⌈n/2⌉; and a local that takes the
results of the calls, which are not used. -/
registers [Len, Start, Free, Half, Unused]

end MergeSort

open MergeSort in
/-- sort(n, a, fr).  The parameters are the procedure numbers of sort itself, half, merge and
copy. -/
def sortBody (pSort pHalf pMerge pCopy : ℕ) : Stmt :=
  .ite (k 1 <' v Len) (
    .call pHalf [v Len] Half ;;
    .call pSort [v Half, v Start, v Free] Unused ;;
    .call pSort [v Len -' v Half, v Start +' v Half, v Free] Unused ;;
    .call pMerge [v Start, v Half, v Start +' v Half, v Len -' v Half, v Free] Unused ;;
    .call pCopy [v Free, v Start, v Len] Unused) .skip

/-- The time of sort. -/
def sortTime (n : ℕ) : ℕ := 61 * (n * Nat.clog 2 n) + 74 * (n - 1) + 4

namespace MergeSort

/-- The recursion for n ⌈log₂ n⌉. -/
theorem clog_split {n : ℕ} (hn : 2 ≤ n) :
    (n + 1) / 2 * Nat.clog 2 ((n + 1) / 2) + (n - (n + 1) / 2) * Nat.clog 2 (n - (n + 1) / 2) + n
      ≤ n * Nat.clog 2 n := by
  have h1 : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
    simpa using Nat.clog_of_two_le (b := 2) (by norm_num) hn
  have h2 : Nat.clog 2 (n - (n + 1) / 2) ≤ Nat.clog 2 ((n + 1) / 2) :=
    Nat.clog_mono_right 2 (by omega)
  have hh : (n + 1) / 2 ≤ n := by omega
  calc
    _ ≤ (n + 1) / 2 * Nat.clog 2 ((n + 1) / 2) + (n - (n + 1) / 2) * Nat.clog 2 ((n + 1) / 2) + n := by
      gcongr
    _ = _ := by rw [← Nat.add_mul, Nat.add_sub_of_le hh, h1, Nat.mul_succ]

/-- The program holds the four procedures. -/
structure Procs (P : Program) (pSort pHalf pMerge pCopy : ℕ) : Prop where
  sort : P[pSort]? = some (sortBody pSort pHalf pMerge pCopy)
  half : P[pHalf]? = some halfBody
  merge : P[pMerge]? = some mergeBody
  copy : P[pCopy]? = some copyBody

/-- The recursion for the number of steps. -/
theorem time_split {n : ℕ} (hn : 2 ≤ n) :
    61 * n + 70 + sortTime ((n + 1) / 2) + sortTime (n - (n + 1) / 2) ≤ sortTime n := by
  have := clog_split hn
  unfold sortTime
  omega

/-- What sort leaves: a sorted permutation of the list L at a; of the cells below fr only those of
the list may have changed. -/
def Sorted (μ : ℕ → ℤ) (a fr : ℕ) (L : List ℤ) (μ' : ℕ → ℤ) : Prop :=
  (∃ L' : List ℤ, Seg μ' a L' ∧ L'.Perm L ∧ L'.Pairwise (· ≤ ·)) ∧
    KeptBut μ μ' fr a L.length

variable {pSort pHalf pMerge pCopy : ℕ}

/-- **sort(n, a, fr)** leaves a sorted permutation of the list at a.  Of the cells below fr only the
n cells from a may change; the n cells from fr are used. -/
theorem _root_.Light.sort_meets (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) {a fr : ℕ} {L : List ℤ} {μ : ℕ → ℤ}
    (hseg : Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space) :
    ∀ d, d + Nat.clog 2 L.length + 1 ≤ lim.depth →
      Meets lim P pSort d [L.length, a, fr] μ (sortTime L.length) fun _ => Sorted μ a fr L := by
  induction he : L.length using Nat.strong_induction_on generalizing a L μ with
  | _ n ih =>
    subst he
    intro d hd
    refine Meets.of_body C.sort ?_
    unfold sortBody
    refine Ends.iteLast (fun hc => ?_) (fun hc => Ends.skip ?_) (hT := by exact Nat.le_of_ble_eq_true rfl)
    · have hn : 1 < L.length := by simpa using hc
      have ht := time_split hn
      have hc : Nat.clog 2 L.length = Nat.clog 2 ((L.length + 1) / 2) + 1 := by
        simpa using Nat.clog_of_two_le (b := 2) (by norm_num) hn
      have hhalf := half_meets (lim := lim) (d := d + 1) C.half μ (h := L.length) (by omega)
      generalize hh : (L.length + 1) / 2 = h at *
      have hl : (L.take h).length = h := by simp; omega
      have hr : (L.drop h).length = L.length - h := by simp
      have recurse (a' : ℕ) (L' : List ℤ) (ν : ℕ → ℤ)
          (hL' : L'.length ≤ h) (hs : Seg ν a' L') (ha : a' + L'.length ≤ fr) :=
        ih L'.length (by omega) hs ha (by omega) rfl (d + 1)
          (by have := Nat.clog_mono_right 2 hL'; omega)
      light_call hhalf with _ μ₀ ⟨rfl, hμ₀⟩
      subst μ₀
      have hsort := recurse a (L.take h) μ hl.le (hseg.take h) (by omega)
      rw [hl] at hsort
      light_call hsort with _ μ₁ ⟨⟨S₁, hS₁, hP₁, hO₁⟩, hk₁⟩
      have hseg₂ := (hseg.drop h).keep (μ' := μ₁) (by light_keep [hl, hr])
      have hsort := recurse (a + h) (L.drop h) μ₁ (by omega) hseg₂ (by omega)
      rw [hr] at hsort
      light_call hsort with _ μ₂ ⟨⟨S₂, hS₂, hP₂, hO₂⟩, hk₂⟩
      have h₁ := hP₁.length_eq.trans hl
      have h₂ := hP₂.length_eq.trans hr
      have hm : (S₁.merge S₂).length = L.length := by simp; omega
      have hmerge := merge_meets (d := d + 1) C.merge (a := a) (b := a + h) (dst := fr) (l := S₁)
        (r := S₂) ⟨hw, hS₁.keep (by light_keep [hl, hr, h₁]), hS₂, by omega, by omega,
          by omega, Or.inl (by omega), Or.inl (by omega)⟩
      rw [h₁, h₂, show h + (L.length - h) = L.length by omega] at hmerge
      light_call hmerge with _ μ₃ ⟨hseg, hk₃⟩
      light_call (copy_meets C.copy (src := fr) (dst := a) (n := L.length) hw (by omega) (by omega)
        (.inr (by omega))) with _ μ₄ ⟨hcopy, hk₄⟩
      refine ⟨⟨S₁.merge S₂, fun i hi => (hcopy i (by omega)).trans (hseg i hi), ?_, hO₁.merge hO₂⟩,
        by light_keep [hl, hr]⟩
      exact (List.merge_perm_append _).trans ((hP₁.append hP₂).trans (by simp))
    · refine ⟨⟨L, hseg, .refl _, List.pairwise_iff_getElem.mpr ?_⟩, .refl⟩
      simp at hc
      omega

end MergeSort

end Light
