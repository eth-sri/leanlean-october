/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

import ThreeSumApsp.Lang.Registers

import ThreeSumApsp.Lang.Symbolic

public import ThreeSumApsp.Lang.Lib.Filter
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Recursion
public import ThreeSumApsp.Spec.Sec3.Theorem21a.NodeArray
public import ThreeSumApsp.Spec.Sec3.Theorem21a.Passes

/-! Count residues in one pass, use the counts for collisions or heavy elements, then clear the
count cells touched by the recorded keys. -/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec.ChanHeArray Finset

variable {lim : Limits} {P : Program}

/-- Ordered pairs of distinct positions with equal keys. -/
def equalPairs : List ℕ → ℕ
  | [] => 0
  | r :: K => equalPairs K + 2 * K.count r

private theorem equalPairs_snoc (K : List ℕ) (r : ℕ) :
    equalPairs (K ++ [r]) = equalPairs K + 2 * K.count r := by
  induction K <;> grind [equalPairs, cons]

private theorem equalPairs_bound (K : List ℕ) : equalPairs K ≤ K.length * K.length := by
  induction K with
  | nil => decide
  | cons r K ih =>
    simp_all [equalPairs] <;> grind

private theorem equalPairs_eq_sum (K : List ℕ) :
    (equalPairs K : ℤ) = (K.map fun q => (K.count q : ℤ) - 1).sum := by
  induction K with
  | nil => rfl
  | cons r K ih =>
    have h (S : List ℕ) : ((S.map fun q => ((r :: K).count q : ℤ) - 1).sum) =
        ((S.map fun q => (K.count q : ℤ) - 1).sum) + S.count r := by
      induction S <;> grind
    grind [equalPairs]

theorem coll_eq_list {L : List ℤ} (hL : L.Nodup) {Mo : ℕ} (hM : 1 ≤ Mo) :
    (coll L.toFinset Mo : ℤ) = equalPairs (keys Mo L) := by
  rw [equalPairs_eq_sum, coll_eq_sum, List.sum_toFinset _ hL]
  have h : ∀ x ∈ L, ((#(bucket L.toFinset Mo (x % (Mo : ℤ))) - 1 : ℕ) : ℤ)
      = ((keys Mo L).count (x % (Mo : ℤ)).toNat : ℤ) - 1 := by
    intro x hx
    rw [← Int.natCast_toNat_emod hM x, card_bucket hM hL]
    have : 1 ≤ (keys Mo L).count (x % (Mo : ℤ)).toNat :=
      List.count_pos_iff.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
    grind
  rw [Nat.cast_list_sum, List.map_map]
  conv_rhs => rw [keys, List.map_map]
  exact congrArg List.sum (List.map_congr_left fun x hx => h x hx)

/-- An element is heavy exactly if its bucket has at least two elements. -/
theorem mem_heavy_iff {S : Finset ℤ} {Mo : ℕ} {x : ℤ} (hx : x ∈ S) :
    x ∈ heavy S Mo ↔ 2 ≤ #(bucket S Mo (x % (Mo : ℤ))) := by
  have hxb : x ∈ bucket S Mo (x % (Mo : ℤ)) := by simp [bucket, hx]
  constructor
  · intro h
    obtain ⟨-, y, hy, hne, hdvd⟩ := Finset.mem_filter.1 h
    have hyb : y ∈ bucket S Mo (x % (Mo : ℤ)) := by
      simp only [bucket, Finset.mem_filter]
      exact ⟨hy, ((natCast_dvd_sub_iff_emod_eq Mo x y).1 hdvd).symm⟩
    exact Finset.one_lt_card.2 ⟨y, hyb, x, hxb, hne⟩
  · intro h
    obtain ⟨y, hy, hne⟩ := Finset.exists_mem_ne h x
    obtain ⟨hyS, hyr⟩ := Finset.mem_filter.1 hy
    exact Finset.mem_filter.2 ⟨hx, y, hyS, hne, (natCast_dvd_sub_iff_emod_eq Mo x y).2 hyr.symm⟩

/-- The heavy elements, as a sublist. -/
def heavyList (Mo : ℕ) (L : List ℤ) : List ℤ :=
  L.filter fun x => decide (2 ≤ (keys Mo L).count (x % (Mo : ℤ)).toNat)

/-- The sublist consists of the heavy elements. -/
theorem heavyList_toFinset {L : List ℤ} (hL : L.Nodup) {Mo : ℕ} (hM : 1 ≤ Mo) :
    (heavyList Mo L).toFinset = heavy L.toFinset Mo := by
  ext x
  simp only [heavyList, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨hx, h⟩
    rw [mem_heavy_iff (List.mem_toFinset.2 hx), ← Int.natCast_toNat_emod hM x, card_bucket hM hL]
    exact h
  · intro h
    have hx : x ∈ L := List.mem_toFinset.1 (heavy_subset _ _ h)
    refine ⟨hx, ?_⟩
    rw [mem_heavy_iff (List.mem_toFinset.2 hx), ← Int.natCast_toNat_emod hM x,
      card_bucket hM hL] at h
    exact h

/-! ## What coll and heavy share: the remainders are counted, used, and removed from the table -/

/-- What coll and heavy assume: the list L at s, a count table of zeros with a cell for each
remainder, both below the free pointer and apart, and the limits. -/
structure BucketPre (lim : Limits) (μ : ℕ → ℤ) (d fr V Mo s cnt cap : ℕ) (L : List ℤ) : Prop where
  modulus_pos : 1 ≤ Mo
  modulus_le : Mo ≤ cap
  bounded : AbsLe L V
  list : Seg μ s L
  zero : ZeroAt μ cnt cap
  belowList : s + L.length ≤ fr
  belowTable : cnt + cap ≤ fr
  apart : Apart s L.length cnt cap
  ok : (collNeed L.length V Mo).Ok lim fr d

/-- The remainders stand at the free pointer, and the table holds their multiplicities. -/
structure Counted (μ : ℕ → ℤ) (fr cnt cap : ℕ) (K : List ℕ) : Prop where
  keys : SegN μ fr K
  counts : ∀ q < cap, μ (cnt + q) = (K.count q : ℤ)

/-- What the need provides: a sum of len counts, which is at most len², and a few more fit in a
word. -/
theorem sq_add_le_word {n V Mo : ℕ} (h : ((wordNeed n V Mo : ℕ) : ℤ) ≤ lim.word) :
    (n : ℤ) * n + 4 * n + 17 ≤ lim.word := by
  have hMV : 1 ≤ (Mo + 1) * (V + 1) := Nat.mul_pos (by omega) (by omega)
  have hle : n * n + 4 * n + 17 ≤ wordNeed n V Mo :=
    calc n * n + 4 * n + 17 ≤ 64 * (n + 1) ^ 2 * 1 := by nlinarith
      _ ≤ 64 * (n + 1) ^ 2 * ((Mo + 1) * (V + 1)) := Nat.mul_le_mul_left _ hMV
      _ = wordNeed n V Mo := by unfold wordNeed; ring
  omega

/-- Clear the touched buckets by traversing the keys again. -/
def ClearSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ {d fr cnt cap : ℕ} {K : List ℕ} {μ : ℕ → ℤ}, Counted μ fr cnt cap K → (∀ k ∈ K, k < cap) →
    cnt + cap ≤ fr → fr + K.length ≤ lim.space → (lim.space : ℤ) ≤ lim.word →
    Meets lim P p d [K.length, fr, cnt] μ (tClear K.length) fun _ ν =>
      ZeroAt ν cnt cap ∧ SameOutside μ ν cnt cap

namespace ClearBuckets
registers [Len, Key, Table, Idx]
end ClearBuckets

open ClearBuckets in
def clearBucketsBody : Stmt :=
  .for Idx (v Len) (.store (v Table +' M (v Key +' v Idx)) (k 0))

theorem clearBuckets_spec {p : ℕ} (hp : P[p]? = some clearBucketsBody) : ClearSpec lim P p := by
  intro d fr cnt cap K μ h hK hc hf hw
  refine .of_body hp ?_
  refine Ends.forFrame (fun i ν => (∀ r < cap, ν (cnt + r) = if r ∈ K.take i then 0 else μ (cnt + r)) ∧
    SameOutside μ ν cnt cap) K.length ⟨by simp, .refl⟩ ?_ ?_ (hT := by light_time [tClear])
  · intro i ν hi inv
    have hk : K[i] < cap := hK _ (List.getElem_mem hi)
    have hr : ν (fr + i) = (K[i] : ℕ) := (inv.2 _ (by omega)).trans (h.keys.getElem hi)
    refine Ends.storeTo (cnt + K[i]) 0 ⟨rfl, ?_, inv.2.update ⟨by omega, by omega⟩ _⟩ (by light_side [hr])
    intro r hr'
    simp only [List.take_succ_eq_append_getElem hi, List.mem_append, List.mem_singleton]
    by_cases he : r = K[i]
    · simp [he]
    · rw [Function.update_of_ne (by omega), inv.1 r hr']
      simp [he]
  · rintro ν ⟨hz, hs⟩
    refine ⟨fun r hr => ?_, hs⟩
    change ν (cnt + r) = 0
    rw [hz r hr, List.take_length, h.counts r hr]
    by_cases he : r ∈ K <;> simp [he, List.count_eq_zero_of_not_mem]

private theorem emodNeed_ok {len V Mo fr d : ℕ} (h : (collNeed len V Mo).Ok lim fr d) :
    (emodNeed V Mo).Ok lim (fr + len) (d + 2) := by
  refine h.mono ?_ (by simp [collNeed, emodNeed]; omega) le_rfl
  have hlen : 1 ≤ (len + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  calc 4 * V + 4 * Mo + 16 ≤ 64 * 1 * (Mo + 1) * (V + 1) := by lia
    _ ≤ 64 * (len + 1) ^ 2 * (Mo + 1) * (V + 1) := by gcongr

/-- Form and count the keys in one traversal. Only the key buffer at `fr` and the count
 table below `fr` are written; the remainder procedure uses scratch past the keys. -/
def CountSpec (lim : Limits) (P : Program) (p : ℕ) : Prop :=
  ∀ {μ d fr V Mo s cnt cap L}, BucketPre lim μ d fr V Mo s cnt cap L → ∀ {sg : ℤ},
    sg = 1 ∨ sg = -1 →
    Meets lim P p (d + 1) [L.length, s, sg, Mo, fr, cnt] μ (tCount L.length V)
      fun r ν => r = equalPairs (keys Mo (L.map (sg * ·))) ∧
        Counted ν fr cnt cap (keys Mo (L.map (sg * ·))) ∧ KeptBut μ ν fr cnt cap

namespace CountLocals
registers [Len, Src, Sign, Modulus, Key, Table, Free, Idx, Rem, Pairs]
end CountLocals

open CountLocals in
def countRound (pEmod : ℕ) : Stmt :=
  .call pEmod [v Sign *' M (v Src +' v Idx), v Modulus, v Free] Rem ;;
  .store (v Key +' v Idx) (v Rem) ;;
  .set Pairs (v Pairs +' k 2 *' M (v Table +' v Rem)) ;;
  .store (v Table +' v Rem) (M (v Table +' v Rem) +' k 1)

open CountLocals in
def countBody (pEmod : ℕ) : Stmt :=
  .set Free (v Key +' v Len) ;; .for Idx (v Len) (countRound pEmod) ;; .set Len (v Pairs)

theorem count_spec {p pEmod : ℕ} (hp : P[p]? = some (countBody pEmod))
    (hE : EmodSpec lim P pEmod) : CountSpec lim P p := by
  intro μ d fr V Mo s cnt cap L C sg hsg
  let K := keys Mo (L.map (sg * ·))
  have hklen : K.length = L.length := by simp [K]
  have hK := keys_lt C.modulus_pos (L.map (sg * ·))
  have hen : (emodNeed V Mo).Ok lim (fr + K.length) (d + 2) :=
    by simpa only [hklen] using emodNeed_ok C.ok
  have hw := C.ok.space
  have hspace := hen.cells
  have hd := hen.depth
  have hw' := hen.word
  have hword := sq_add_le_word C.ok.word
  simp only [emodNeed] at hspace hd hw'
  have hcnt := C.belowTable
  have hsrc := C.belowList
  have hap := C.apart
  let ls (i : ℕ) (z : ℤ × ℤ) : List ℤ :=
    [L.length, s, sg, Mo, fr, cnt, (fr + L.length : ℕ), i, z.1, z.2]
  refine .of_body hp ?_
  unfold countBody
  light_set (fr + L.length : ℕ) using tCount
  let I (i : ℕ) (z : ℤ × ℤ) (ν : ℕ → ℤ) :=
    Counted ν fr cnt cap (K.take i) ∧ KeptBut μ ν fr cnt cap ∧ z.2 = equalPairs (K.take i)
  refine Ends.next _ (Ends.forShape (fun i z ν => ⟨frame (ls i z), ν⟩) I K.length
    (tEmod V + 44) (0, 0) ⟨⟨by simp [SegN], by simpa using fun r hr => C.zero r hr⟩, .refl, rfl⟩ ?_ ?_
    (first := by rw [update_frame_setLocal, ← frame_append_zeros _ 2]; rfl)
    (bound := by intros; light_side [ls, hklen]) (counter := by intros; rfl)
    (next := by intros; simp only [update_frame_setLocal]; rfl) (hT := le_rfl))
    (by light_time [ls, tCount, hklen])
  · rintro i ⟨old, val⟩ ν hi ⟨h, hkeep, hv⟩
    change val = (equalPairs (K.take i) : ℤ) at hv
    have hiL : i < L.length := by omega
    have hr₁ : ν (s + i) = L[i] := (hkeep _ (by omega)).trans (C.list i hiL)
    have hkey : (K[i] : ℕ) = (sg * L[i]) % (Mo : ℤ) :=
      by simpa [K, keys] using Int.natCast_toNat_emod C.modulus_pos (sg * L[i])
    have hki := (hK K[i] (List.getElem_mem hi)).trans_le C.modulus_le
    have hm : |sg * L[i]| ≤ (V : ℤ) := by
      rcases hsg with rfl | rfl <;> simpa using C.bounded.getElem hiL
    have hpm := abs_le.1 hm
    have ha := abs_le.1 (C.bounded.getElem hiL)
    have hval : 0 ≤ val ∧ val ≤ (L.length : ℤ) * L.length := by
      rw [hv]
      refine ⟨by positivity, ?_⟩
      exact_mod_cast (equalPairs_bound _).trans (Nat.mul_le_mul (by simp [hklen]) (by simp [hklen]))
    unfold countRound
    light_call (hE (d + 2) (fr + K.length) V Mo (sg * L[i]) ν C.modulus_pos hm hen)
      using ls, hklen, hr₁ with _ ν' ⟨rfl, hk⟩
    rw [← hkey]
    have hb : cnt + K[i] < fr + K.length := by omega
    have hc : Function.update ν' (fr + i) (K[i] : ℕ) (cnt + K[i]) = (K.take i).count K[i] := by
      rw [Function.update_of_ne (by omega), hk _ hb, h.counts _ hki]
    have hn : (K.take i).count K[i] ≤ i := List.count_le_length.trans (by simp)
    light_steps using ls, hc
    refine ⟨⟨_, _⟩, _, rfl, ⟨?_, ?_⟩, ?_, ?_⟩
    · have hn : (K.take (i + 1)).length ≤ K.length := by simp
      have hstep := SegN.take_succ (h.keys.keep (fun b hb => hk b (by
        have := List.length_take_le i K
        omega))) hi
      simpa only [List.getD_eq_getElem _ _ hi] using
        Seg.update_out (b := cnt + K[i]) hstep (Or.inl (by omega)) (((K.take i).count K[i] : ℤ) + 1)
    · intro r hr
      rw [List.count_take_succ K r hi]
      by_cases e : r = K[i]
      · subst r; simp
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), hk _ (by omega)]
        simpa [Ne.symm e] using h.counts r hr
    · exact ((hkeep.then hk (by omega)).write (b := fr + i) (by omega) _).write
        (b := cnt + K[i]) (by omega) _
    · change val + 2 * ((K.take i).count K[i] : ℤ) = (equalPairs (K.take (i + 1)) : ℤ)
      rw [List.take_succ_eq_append_getElem hi, equalPairs_snoc, hv]
      push_cast
      rfl
  · rintro ⟨r, val⟩ ν ⟨hc, hkeep, hv⟩
    rw [List.take_length] at hc hv
    light_set val using ls, tCount, hklen
    exact ⟨hv, hc, hkeep⟩

/-- The unsigned call is used by the collision and heavy-element routines. -/
theorem BucketPre.count_unsigned {μ d fr V Mo s cnt cap L p}
    (C : BucketPre lim μ d fr V Mo s cnt cap L) (h : CountSpec lim P p) :
    Meets lim P p (d + 1) [L.length, s, 1, Mo, fr, cnt] μ (tCount L.length V)
      fun r ν => r = equalPairs (keys Mo L) ∧ Counted ν fr cnt cap (keys Mo L) ∧ KeptBut μ ν fr cnt cap := by
  simpa using h C (Or.inl (Eq.refl (1 : ℤ)))

/-- A table that held zeros and holds zeros again has not changed. -/
theorem sameOn_of_zeroAt {R : ℕ → Prop} {μ μ' : ℕ → ℤ} {cnt cap : ℕ}
    (h : SameOn (fun b => R b ∧ Outside cnt cap b) μ μ') (hz : ZeroAt μ cnt cap)
    (hz' : ZeroAt μ' cnt cap) : SameOn R μ μ' := fun b hb => by
  by_cases hin : Outside cnt cap b
  · aesop
  · obtain ⟨q, rfl⟩ : ∃ q, b = cnt + q := ⟨b - cnt, by omega⟩
    rw [hz q (by omega), hz' q (by omega)]

/-- What is counted stays counted if neither the remainders nor the table change. -/
theorem Counted.of_sameOutside {μ μ' : ℕ → ℤ} {fr cnt cap a n : ℕ} {K : List ℕ}
    (h : Counted μ fr cnt cap K) (hs : SameOutside μ μ' a n) (hfr : a + n ≤ fr)
    (hap : Apart a n cnt cap) :
    Counted μ' fr cnt cap K :=
  ⟨h.keys.of_sameOutside hs (Or.inr hfr),
    fun q hq => (hs _ (by omega)).trans (h.counts q hq)⟩

/-- What coll and heavy are given, in the form in which they use it: the set is a list without
repetitions. -/
theorem BucketMem.exists_pre {μ : ℕ → ℤ} {d fr V Mo s len cnt cap : ℕ} {S : Finset ℤ}
    (h : BucketMem μ fr V Mo s len cnt cap S) (hok : (collNeed len V Mo).Ok lim fr d) :
    ∃ L : List ℤ, L.length = len ∧ L.Nodup ∧ L.toFinset = S ∧
      BucketPre lim μ d fr V Mo s cnt cap L := by
  obtain ⟨L, rfl, hseg, hnd, rfl⟩ := h.set
  exact ⟨L, rfl, hnd, rfl, h.modulus_pos, h.modulus_le,
    fun x hx => h.bdd x (List.mem_toFinset.2 hx), hseg, h.zero, h.belowSet, h.belowTable, h.apart,
    hok⟩

namespace BucketPre

variable {μ μ₁ : ℕ → ℤ} {d fr V Mo s cnt cap pCount pClear : ℕ} {L : List ℤ} {K : List ℕ}

/-- Clear the counts, leaving the rest of the memory alone. -/
theorem clear_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hClear : ClearSpec lim P pClear)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < Mo) (h : Counted μ₁ fr cnt cap K) :
    Meets lim P pClear (d + 1) [L.length, fr, cnt] μ₁ (tClear L.length) fun _ μ₂ =>
      ZeroAt μ₂ cnt cap ∧ SameOutside μ₁ μ₂ cnt cap := by
  have hc := C.ok.cells
  simp only [collNeed] at hc
  simpa only [hlen] using hClear (d := d + 1) h (fun q hq => (hlt q hq).trans_le C.modulus_le)
    C.belowTable (by omega) C.ok.space

end BucketPre

/-! ## coll -/

namespace Coll
registers [Len / Result, Src, Modulus, Count, Free, Pairs, Unread]
end Coll

open Coll in
/-- Count equal-key pairs while filling the buckets, then restore the zero table. -/
def collBody (pCount pClear : ℕ) : Stmt :=
  .call pCount [v Len, v Src, k 1, v Modulus, v Free, v Count] Pairs ;;
  .call pClear [v Len, v Free, v Count] Unread ;;
  .set Result (v Pairs)

/-- **coll** meets its specification. -/
theorem coll_spec {p pCount pClear : ℕ} (hP : P[p]? = some (collBody pCount pClear))
    (hCount : CountSpec lim P pCount) (hClear : ClearSpec lim P pClear) : CollSpec lim P p := by
  intro d fr V Mo s len cnt cap S μ hmem hok
  obtain ⟨L, rfl, hnd, rfl, C⟩ := hmem.exists_pre hok
  refine ⟨_, hP, ?_⟩
  have hM := C.modulus_pos
  have hw := hok.space
  have hword := sq_add_le_word hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  simp only [collNeed] at hcells hdepth
  light_call (C.count_unsigned hCount) using tColl with r μ₂ ⟨hr, counted, kept₂⟩
  -- Clear the count table.
  light_call (C.clear_meets hClear (length_keys Mo L) (keys_lt hM L) counted)
    using tColl with _ μ₃ ⟨zero₃, same₃⟩
  light_set r using tColl
  exact ⟨hr.trans (coll_eq_list hnd hM).symm,
    sameOn_of_zeroAt (kept₂.then same₃ fun b hb => ⟨hb, hb.2⟩) C.zero zero₃⟩

/-! ## heavy -/

namespace Heavy

/-- The local variables of heavy: the arguments len, s, M, out, cnt, fr, the results of the calls,
which are not used, the counter i, and the number j of elements written.  Local 0 also takes the
result. -/
registers [Len / Result, Src, Modulus, Out, Count, Free, Res, Idx, Written]

end Heavy

open Heavy in
def heavyTest : Guard := .atom (k 1 <' M (v Count +' M (v Free +' v Idx)))

open Heavy in
def heavyCopy : Stmt := filterPass Idx Len Out Written heavyTest (M (v Src +' v Idx))

open Heavy in
/-- heavy(len, s, M, out, cnt, fr) writes the remainders to fr, counts them, copies the heavy
elements, removes the remainders from the table, and returns the number of heavy elements. -/
def heavyBody (pCount pClear : ℕ) : Stmt :=
  .call pCount [v Len, v Src, k 1, v Modulus, v Free, v Count] Res ;;
  heavyCopy ;;
  .call pClear [v Len, v Free, v Count] Res ;;
  .set Result (v Written)

/-- The test of heavy: the remainder of `x` occurs at least twice among the remainders. -/
def isHeavy (Mo : ℕ) (L : List ℤ) (x : ℤ) : Bool :=
  decide (2 ≤ (keys Mo L).count (x % (Mo : ℤ)).toNat)

/-- The heavy elements among the first `i` elements of the list. -/
abbrev heavyPart (Mo : ℕ) (L : List ℤ) (i : ℕ) : List ℤ := Spec.passList (isHeavy Mo L) id L i

/-- The heavy elements among all elements of the list are the list of the heavy elements. -/
theorem heavyPart_length (Mo : ℕ) (L : List ℤ) : heavyPart Mo L L.length = heavyList Mo L := by
  rw [heavyPart, Spec.passList_length, List.map_id]
  rfl

private theorem heavyCopy_ends {d V s Mo out cnt cap fr : ℕ} {r : ℤ} {μ₀ μ : ℕ → ℤ} {L : List ℤ}
    (C : BucketPre lim μ₀ d fr V Mo s cnt cap L) (counted : Counted μ fr cnt cap (keys Mo L))
    (hL : Seg μ s L) (O : HeavyOut fr s cnt cap out L.length) :
    Ends lim P d heavyCopy ⟨frame [L.length, s, Mo, out, cnt, fr, r], μ⟩ (30 * L.length + 10)
      fun σ => ∃ ν, σ = ⟨frame [L.length, s, Mo, out, cnt, fr, r, L.length, (heavyList Mo L).length], ν⟩ ∧
        Seg ν out (heavyList Mo L) ∧ SameOutside μ ν out L.length := by
  have hcells := C.ok.cells
  light_facts C O C.ok
  simp only [collNeed] at hcells
  have hword := sq_add_le_word C.ok.word
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  unfold heavyCopy
  refine Ends.filterPass _ _ (fun i D => D = heavyPart Mo L i) rfl ?_ ?_ C.ok.space
    (by omega) rfl rfl (hT := by light_time [filterStep, heavyTest])
  · intro i D ν hi hD H
    have hh := H.size
    have hiK : i < (keys Mo L).length := by rwa [length_keys]
    have hq : (keys Mo L)[i] < Mo := keys_lt C.modulus_pos _ _ (List.getElem_mem hiK)
    have hkey := (H.same (fr + i) (by omega)).trans (counted.keys.getElem hiK)
    have hcount := (H.same (cnt + (keys Mo L)[i]) (by omega)).trans (counted.counts _ (by omega))
    have hread := (H.same (s + i) (by omega)).trans (hL i hi)
    have hqi : (keys Mo L)[i] = (L[i] % (Mo : ℤ)).toNat := by simp [keys]
    subst D
    refine ⟨by light_side [heavyTest, hkey], by light_side, ?_, ?_⟩
    · intro hs
      have ht : 2 ≤ (keys Mo L).count (keys Mo L)[i] := Nat.succ_le_of_lt (by simpa [heavyTest, hkey, hcount] using hs)
      simpa [List.getD_eq_getElem _ _ hi, hread] using
        (Spec.passList_succ_of id hi (by simpa [isHeavy, ← hqi] using ht)).symm
    · intro hs
      have ht : ¬ 2 ≤ (keys Mo L).count (keys Mo L)[i] := fun he =>
        hs (by simpa [heavyTest, hkey, hcount] using Nat.lt_of_succ_le he)
      exact (Spec.passList_succ_of_not id hi (by simpa [isHeavy, ← hqi] using ht)).symm
  · rintro D ν rfl H
    simp only [heavyPart_length] at H ⊢
    exact ⟨ν, by simp [filterState, update_frame_setLocal], H.seg, H.same.mono le_rfl (Nat.add_le_add_left H.size _)⟩

/-- **heavy** meets its specification. -/
theorem heavy_spec {p pCount pClear : ℕ} (hP : P[p]? = some (heavyBody pCount pClear))
    (hCount : CountSpec lim P pCount) (hClear : ClearSpec lim P pClear) : HeavySpec lim P p := by
  intro d fr V Mo s len out cnt cap S μ hmem O hok
  obtain ⟨L, rfl, hnd, rfl, C⟩ := hmem.exists_pre hok
  refine ⟨_, hP, ?_⟩
  have hout := O.below
  have hapc := O.apartTable
  have hM := C.modulus_pos
  light_facts C hok
  have hword := sq_add_le_word hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  have hsq : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  simp only [collNeed] at hcells hdepth
  light_call (C.count_unsigned hCount) using tHeavy with r μ₂ ⟨-, counted, kept₂⟩
  have hseg₂ : Seg μ₂ s L := C.list.keep
  -- the heavy elements are copied
  light_piece (heavyCopy_ends C counted hseg₂ O) using tHeavy with _ ⟨μ₃, rfl, written, same₃⟩
  -- Clear the count table.
  light_call (C.clear_meets hClear (length_keys Mo L) (keys_lt hM L)
    (counted.of_sameOutside same₃ hout hapc)) using tHeavy with _ μ₄ ⟨zero₄, same₄⟩
  have hnd' : (heavyList Mo L).Nodup := hnd.filter _
  have hcard : #(heavy L.toFinset Mo) = (heavyList Mo L).length := by
    rw [← heavyList_toFinset hnd hM, List.toFinset_card_of_nodup hnd']
  have hle : (heavyList Mo L).length ≤ L.length := List.length_filter_le _ _
  -- return the number of heavy elements
  refine Ends.setTo (#(heavy L.toFinset Mo) : ℤ) ⟨by simp,
    ⟨heavyList Mo L, hcard.symm, written.keep,
      hnd', heavyList_toFinset hnd hM⟩, ?_⟩ (by simp [hcard])
    (by simp [tHeavy]; omega)
  exact sameOn_of_zeroAt ((kept₂.then same₃ fun b hb => ⟨⟨hb.1.1, hb.2⟩, hb.1.2⟩).then same₄
    fun b hb => ⟨hb, hb.2⟩) C.zero zero₄

end Light.Sec3.ChanHe
