/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Lib.Copy
import ThreeSumApsp.Lang.Lib.Logs
import ThreeSumApsp.Lang.Lib.Merge

/-!
# Merge sort

sort(n, a, fr) sorts the n cells from a in place, in ascending order (`sort_meets`).  It is the
recursive merge sort: sort the first ⌈n/2⌉ cells, sort the rest, merge the two halves into the n
cells from the free pointer fr, and copy them back.  It calls half, merge and copy.

The proof is an induction on n.  `body_ends` treats the body of the procedure, given that the
procedure sorts the lists of half the length, and `join_ends` its last two calls; `sorted_merge`
says that what the four calls leave is a sorted permutation of the list.  The number of steps,
`sortTime n`, is of the order n log n (`clog_split`, `time_split`), and the calls are nested
⌈log₂ n⌉ + 1 deep.  Numbers are only compared and copied, so their size does not matter.
-/


namespace Light

variable {lim : Limits} {P : Program}

namespace MergeSort

/- The local variables of sort: the arguments n, a and fr; h = ⌈n/2⌉; and a local that takes the
results of the calls, which are not used. -/
slots Len Start Free Half Unused

end MergeSort

open MergeSort in
/-- The two sorted halves are merged into the cells from fr and copied back. -/
def sortJoin (pMerge pCopy : ℕ) : Stmt :=
  .call pMerge [v Start, v Half, v Start +' v Half, v Len -' v Half, v Free] Unused ;;
  .call pCopy [v Free, v Start, v Len] Unused

open MergeSort in
/-- sort(n, a, fr).  The parameters are the procedure numbers of sort itself, half, merge and
copy. -/
def sortBody (pSort pHalf pMerge pCopy : ℕ) : Stmt :=
  .ite (k 1 <' v Len) (
    .call pHalf [v Len] Half ;;
    .call pSort [v Half, v Start, v Free] Unused ;;
    .call pSort [v Len -' v Half, v Start +' v Half, v Free] Unused ;;
    sortJoin pMerge pCopy) .skip

/-- The time of sort. -/
def sortTime (n : ℕ) : ℕ := 61 * (n * Nat.clog 2 n) + 74 * (n - 1) + 4

namespace MergeSort

variable {n : ℕ}

/-- The recursion for n ⌈log₂ n⌉. -/
theorem clog_split (hn : 2 ≤ n) :
    (n + 1) / 2 * Nat.clog 2 ((n + 1) / 2) + (n - (n + 1) / 2) * Nat.clog 2 (n - (n + 1) / 2) + n
      ≤ n * Nat.clog 2 n := by
  have h1 : Nat.clog 2 n = Nat.clog 2 ((n + 1) / 2) + 1 := by
    grind [Nat.clog_of_two_le]
  have h2 : Nat.clog 2 (n - (n + 1) / 2) ≤ Nat.clog 2 ((n + 1) / 2) :=
    Nat.clog_mono_right 2 (by omega)
  have hh : (n + 1) / 2 ≤ n := by omega
  rw [h1]
  generalize (n + 1) / 2 = h at *
  generalize Nat.clog 2 h = c at *
  have a1 : (n - h) * Nat.clog 2 _ ≤ (n - h) * c := Nat.mul_le_mul_left _ h2
  have a2 : h * c + (n - h) * c = n * c := by
    rw [← Nat.add_mul]
    simp_all
  linarith

/-- The program holds the four procedures. -/
structure Procs (P : Program) (pSort pHalf pMerge pCopy : ℕ) : Prop where
  sort : P[pSort]? = some (sortBody pSort pHalf pMerge pCopy)
  half : P[pHalf]? = some halfBody
  merge : P[pMerge]? = some mergeBody
  copy : P[pCopy]? = some copyBody

/-- The recursion for the number of steps. -/
theorem time_split (hn : 2 ≤ n) :
    61 * n + 70 + sortTime ((n + 1) / 2) + sortTime (n - (n + 1) / 2) ≤ sortTime n := by
  have := clog_split hn
  unfold sortTime
  omega

/-- What sort leaves: a sorted permutation of the list L at a; of the cells below fr only those of
the list may have changed. -/
def Sorted (μ : ℕ → ℤ) (a fr : ℕ) (L : List ℤ) (μ' : ℕ → ℤ) : Prop :=
  (∃ L' : List ℤ, Seg μ' a L' ∧ L'.Perm L ∧ L'.Pairwise (· ≤ ·)) ∧
    KeptBut μ μ' fr a L.length

variable {μ : ℕ → ℤ} {a fr : ℕ} {L : List ℤ}

/-- A list of at most one number is sorted. -/
theorem sorted_refl (hseg : Seg μ a L) (hL : L.length ≤ 1 := by simp_all) :
    Sorted μ a fr L μ := by
  refine ⟨⟨L, hseg, .refl _, ?_⟩, .refl⟩
  match L, hL with
  | [], _ => decide
  | [x], _ => simp

variable {h : ℕ} {S₂ S₁ : List ℤ}

/-- The two halves are sorted one after the other, merged into the cells from fr, and copied
back. -/
theorem sorted_merge {μ₁ μ₂ μ₃ μ₄ : ℕ → ℤ} {m : ℕ} (hh : h ≤ L.length)
    (hP₁ : S₁.Perm (L.take h)) (hO₁ : S₁.Pairwise (· ≤ ·))
    (hk₁ : KeptBut μ μ₁ fr a (L.take h).length) (hP₂ : S₂.Perm (L.drop h))
    (hO₂ : S₂.Pairwise (· ≤ ·)) (hk₂ : KeptBut μ₁ μ₂ fr (a + h) (L.drop h).length)
    (hk₃ : SameOutside μ₂ μ₃ fr m) (hS₄ : Seg μ₄ a (S₁.merge S₂))
    (hk₄ : SameOutside μ₃ μ₄ a L.length) : Sorted μ a fr L μ₄ := by
  refine ⟨⟨S₁.merge S₂, hS₄, ?_, hO₁.merge hO₂⟩, fun c hc => ?_⟩
  · calc (S₁.merge S₂).Perm _ := List.merge_perm_append _
      _ |>.Perm (L.take h ++ L.drop h) := hP₁.append hP₂
      _ = L := by simp
  · have hl₁ : (L.take h).length = h := by simp_all
    have hl₂ : (L.drop h).length = L.length - h := by simp
    rw [hk₄ c hc.2, hk₃ c (Or.inl hc.1), hk₂ c ⟨hc.1, by omega⟩, hk₁ c ⟨hc.1, by omega⟩]

variable {pSort pHalf pMerge pCopy : ℕ}

variable {d : ℕ}

/-- Two lists, one after the other in the memory, are merged into the cells from fr and copied
back. -/
theorem join_ends (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) {r : ℤ}     (hl₁ : S₁.length = h) (hl₂ : S₂.length = n - h) (hh : h ≤ n) (hn : 1 ≤ n) (hS₁ : Seg μ a S₁)
    (hS₂ : Seg μ (a + h) S₂) (haf : a + n ≤ fr) (hfr : fr + n ≤ lim.space) (hd : d < lim.depth) :
    Ends lim P d (sortJoin pMerge pCopy) ⟨frame [n, a, fr, h, r], μ⟩ (56 * n + 34) fun σ' =>
      ∃ μ' : ℕ → ℤ, SameOutside μ μ' fr n ∧ Seg σ'.mem a (S₁.merge S₂) ∧
        SameOutside μ' σ'.mem a n := by
  have hlm : (S₁.merge S₂).length = n := by simp_all
  -- merge(a, h, a + h, n - h, fr)
  have hmerge := merge_meets (d := d + 1) C.merge (dst := fr) ⟨hw, hS₁, hS₂, by omega, by omega, by omega, by omega, by omega⟩
  rw [hl₁, hl₂, show h + (n - h) = n by omega] at hmerge
  light_call hmerge with _ μ₁ ⟨hseg, hk₁⟩
  -- copy(fr, a, n)
  light_call (copy_meets C.copy (src := fr) (dst := a) (n := n) hw (by omega) (by omega)
    (by omega)) with _ μ₂ ⟨hcopy, hk₂⟩
  exact ⟨μ₁, hk₁, fun i hi => (hcopy i (by omega)).trans (by tauto), hk₂⟩

/-- The body of sort, given that the procedure sorts the lists of at most half the length, rounded
up. -/
theorem body_ends (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)     (hseg : Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space)
    (hd : d < lim.depth)
    (ih : ∀ (a' : ℕ) (L' : List ℤ) (μ' : ℕ → ℤ), 1 < L.length → 2 * L'.length ≤ L.length + 1 →
      Seg μ' a' L' → a' + L'.length ≤ fr →
      Meets lim P pSort (d + 1) [L'.length, a', fr] μ' (sortTime L'.length) fun _ =>
        Sorted μ' a' fr L') :
    Ends lim P d (sortBody pSort pHalf pMerge pCopy) ⟨frame [L.length, a, fr], μ⟩
      (sortTime L.length) fun σ' => Sorted μ a fr L σ'.mem := by
  -- if 1 < n
  refine Ends.iteLast (fun hc => ?_) (by simp_all [Ends.skip, sorted_refl])
    (hT := by simp [sortTime])
  have hn : 1 < L.length := by simp_all
  have htime := time_split hn
  have hhalf := half_meets (d := d + 1) C.half μ (h := L.length)
    (le_trans (by omega) hw)
  have hlt : (L.length + 1) / 2 < L.length := by omega
  have htwice : 2 * ((L.length + 1) / 2) ≤ L.length + 1 := by omega
  have htwice' : L.length ≤ 2 * ((L.length + 1) / 2) := by omega
  generalize (L.length + 1) / 2 = h at *
  have hl₁ : (L.take h).length = h := by grind
  have hl₂ : (L.drop h).length = L.length - h := by simp
  -- h := half(n)
  light_call hhalf with _ μ₀ ⟨rfl, hμ₀⟩
  obtain rfl := hμ₀.symm
  -- sort(h, a, fr)
  have hsort₁ := ih a _ μ hn (by omega) (hseg.take h) (by omega)
  rw [hl₁] at hsort₁
  light_call hsort₁ with _ μ₁ ⟨⟨S₁, hS₁, hP₁, hO₁⟩, hk₁⟩
  light_call (ih _ _ μ₁ hn (by omega) ((hseg.drop h).congr fun i hi => hk₁ _ ⟨by omega, by omega⟩) (by omega)) with _ μ₂ ⟨⟨S₂, hS₂, hP₂, hO₂⟩, hk₂⟩
  have hlS₁ := hP₁.length_eq
  apply (join_ends C hw (hP₁.length_eq.trans hl₁) (hP₂.length_eq.trans hl₂) hlt.le hn.le (hS₁.congr fun i hi => hk₂ _ ⟨by omega, by omega⟩) hS₂
    haf hfr hd).mono (by light_time)
  rintro _ ⟨μ₃, hk₃, hS₄, hk₄⟩
  exact sorted_merge hlt.le hP₁ hO₁ hk₁ hP₂ hO₂ hk₂ hk₃ hS₄ hk₄

/-- **sort(n, a, fr)** leaves a sorted permutation of the list at a.  Of the cells below fr only the
n cells from a may change; the n cells from fr are used. -/
theorem _root_.Light.sort_meets (C : Procs P pSort pHalf pMerge pCopy)
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word)     (hseg : Seg μ a L) (haf : a + L.length ≤ fr) (hfr : fr + L.length ≤ lim.space) :
    ∀ d, d + Nat.clog 2 L.length + 1 ≤ lim.depth →
      Meets lim P pSort d [L.length, a, fr] μ (sortTime L.length) fun _ => Sorted μ a fr L := by
  induction hn : L.length using Nat.strong_induction_on generalizing a L μ with
  | _ n ih =>
    subst hn
    intro d hd
    refine Meets.of_body C.sort (body_ends C hw h1 hseg haf hfr (by omega)
      fun a' L' μ' hn hhalf hseg' haf' =>
        ih L'.length (by omega) hseg' haf' (by omega) rfl _ ?_)
    -- one level of calls fewer for half the length
    have hclog : Nat.clog 2 L.length = Nat.clog 2 ((L.length + 1) / 2) + 1 := by
      grind [Nat.clog_of_two_le]
    have := Nat.clog_mono_right 2 (by omega : L'.length ≤ (L.length + 1) / 2)
    omega
