module

public import PaperStatements
public import ThreeSumApsp.Util.Index
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Contracts
public import ThreeSumApsp.Sec3.Theorem21a.ChanHe.Recursion
public import ThreeSumApsp.Spec.Sec3.Theorem21a.Passes
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeMemory

@[expose] public section

section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The array of a node of the reduction after Chan and He, from lists

For Theorem 21(a), after [CH20, Theorem 5.1].  The one-array instance of a node of the reduction
from 3SUM to Convolution-3SUM (`ChanHe.Node.oneArray`) is
defined through the buckets of three finite sets.  A program has each set as a list without
repetitions, computes the list of the remainders (`keys`), and counts how often each remainder
occurs.  In these terms:

* the size of a bucket is the number of times its remainder occurs (`card_bucket`);
* a cell of `arr` holds the number with that remainder if the remainder occurs once
  (`arr_of_count_eq_one`), and the padding value otherwise (`arr_of_count_ne_one`, `arr_of_le`);
* the cells `4i`, `4i + 1`, `4i + 2`, `4i + 3` of `oneArray` hold a constant and cell `i` of the
  three arrays, each shifted (`oneArray_cells`).
-/


namespace ThreeSumApsp.Spec.ChanHeArray

open ChanHe Finset

/-- The remainders of the numbers of a list, as natural numbers. -/
def keys (M : ℕ) (L : List ℤ) : List ℕ := L.map fun x => (x % (M : ℤ)).toNat

/-- Each number has one remainder. -/
@[simp] theorem length_keys (M : ℕ) (L : List ℤ) : (keys M L).length = L.length := by simp [keys]

/-- The remainders are below `M`. -/
theorem keys_lt {M : ℕ} (hM : 1 ≤ M) (L : List ℤ) : ∀ r ∈ keys M L, r < M := by
  intro r hr
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hr
  exact Int.toNat_emod_lt hM x

/-- The list of the remainders, as integers. -/
theorem map_cast_keys {M : ℕ} (hM : 1 ≤ M) (L : List ℤ) :
    (keys M L).map (fun r : ℕ => (r : ℤ)) = L.map fun x => x % (M : ℤ) := by
  rw [keys, List.map_map]
  exact List.map_congr_left fun x _ => Int.natCast_toNat_emod hM x

/-- The size of a bucket is the number of times its remainder occurs in the list of the
remainders. -/
theorem card_bucket {M : ℕ} (hM : 1 ≤ M) {L : List ℤ} (hL : L.Nodup) (r : ℕ) :
    #(bucket L.toFinset M r) = (keys M L).count r := by
  have hfilter : bucket L.toFinset M (r : ℤ) =
      (L.filter fun x => decide (x % (M : ℤ) = (r : ℤ))).toFinset := by
    ext x
    simp [bucket]
  rw [hfilter, List.toFinset_card_of_nodup (hL.filter _), keys, List.count_eq_countP,
    List.countP_map, List.countP_eq_length_filter]
  congr 1
  refine List.filter_congr fun x _ => ?_
  have := Int.natCast_toNat_emod hM x
  change decide (x % (M : ℤ) = (r : ℤ)) = decide ((x % (M : ℤ)).toNat = r)
  exact decide_eq_decide.2 (by omega)

/-- A cell whose remainder occurs once holds the number with that remainder. -/
theorem arr_of_count_eq_one {M : ℕ} (hM : 1 ≤ M) {L : List ℤ} (hL : L.Nodup) (pd : ℤ) {j : ℕ}
    (hj : j < L.length) (hc : (keys M L).count (L[j] % (M : ℤ)).toNat = 1) :
    arr L.toFinset M pd (L[j] % (M : ℤ)).toNat = L[j] := by
  rw [arr, card_bucket hM hL, if_pos hc]
  rw [← card_bucket hM hL] at hc
  obtain ⟨a, ha⟩ := card_eq_one.1 hc
  have hmem : L[j] ∈ bucket L.toFinset M ((L[j] % (M : ℤ)).toNat : ℕ) := by
    rw [bucket, mem_filter, List.mem_toFinset]
    exact ⟨List.getElem_mem hj, (Int.natCast_toNat_emod hM _).symm⟩
  rw [ha] at hmem ⊢
  rw [sum_singleton, mem_singleton.1 hmem]

/-- A cell whose remainder does not occur exactly once holds the padding value. -/
theorem arr_of_count_ne_one {M : ℕ} (hM : 1 ≤ M) {L : List ℤ} (hL : L.Nodup) (pd : ℤ) {r : ℕ}
    (hc : (keys M L).count r ≠ 1) : arr L.toFinset M pd r = pd := by
  rw [arr, card_bucket hM hL, if_neg hc]

/-- The cells from `M` on hold the padding value. -/
theorem arr_of_le {M : ℕ} (hM : 1 ≤ M) (S : Finset ℤ) (pd : ℤ) {i : ℕ} (hi : M ≤ i) :
    arr S M pd i = pd := by
  have hempty : bucket S M i = ∅ := by
    rw [bucket, filter_eq_empty_iff]
    intro x _ hx
    have : x % (M : ℤ) < M := Int.emod_lt_of_pos _ (by exact_mod_cast hM)
    omega
  rw [arr, hempty, if_neg (by simp)]

/-- The four kinds of cells of the one-array instance of a node.  Here `6V + 4` is the number
`G = 3W + 1` for `W = 2V + 1`. -/
theorem oneArray_cells (ν : Node) (V i : ℕ) :
    ν.oneArray V (4 * i) = 10 * (6 * V + 4) ∧
      ν.oneArray V (4 * i + 1) = arr ν.S₁ ν.M (2 * V + 1) i + (6 * V + 4) ∧
      ν.oneArray V (4 * i + 2) = arr ν.S₂ ν.M (2 * V + 1) i + 3 * (6 * V + 4) ∧
      ν.oneArray V (4 * i + 3) = arrZ ν.S₃ ν.M V i + 4 * (6 * V + 4) := by
  have hcell : ∀ r < 4, (4 * i + r) % 4 = r ∧ (4 * i + r) / 4 = i := fun r hr => by omega
  have hzero : 4 * i % 4 = 0 := Nat.mul_mod_right 4 i
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Node.oneArray, ChanHe.oneArray, arrXY, pad, hzero, hcell 1 (by norm_num),
      hcell 2 (by norm_num), hcell 3 (by norm_num)] <;> norm_num <;> ring

end ThreeSumApsp.Spec.ChanHeArray

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# 3SUM from Convolution-3SUM: remainders, counts, collisions, heavy elements

Four routines of the reduction of [CH20, Theorem 5.1] (for Theorem 21(a)).
They hash a set of integers modulo M.

* resid writes the remainders of the elements of a set (`resid_spec`).
* tally adds the remainders to a table of counts, or removes them from it (`tally_spec`).
* coll returns the number of colliding ordered pairs (`coll_spec`): by `coll_eq_list` it is the sum,
  over the elements, of the size of the element's bucket minus 1.
* heavy extracts the elements that are not alone in their bucket (`heavy_spec`,
  `heavyList_toFinset`).

In the statements the modulus is Mo, since in a program text M (…) reads a cell of the memory.
`keys M L` is the list of the remainders x % M of the numbers of L, as natural numbers, and `SegN`
is `Seg` for a list of natural numbers.

coll and heavy begin and end in the same way: resid writes the remainders to the free pointer, tally
counts them (`Counted`), a loop reads the counts, and tally removes them, so that the table holds
zeros again.  The three calls are `BucketPre.resid_meets`, `count_meets` and `uncount_meets`.
-/


namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec.ChanHeArray Finset

variable {lim : Limits} {P : Program}

/-! ## resid -/

namespace Resid

/-- The local variables of resid: the arguments len, s, sg, M, key, fr, the counter i, and the
remainder. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Sign : ℕ := 2
@[inherit_doc Len] abbrev Modulus : ℕ := 3
@[inherit_doc Len] abbrev Key : ℕ := 4
@[inherit_doc Len] abbrev Free : ℕ := 5
@[inherit_doc Len] abbrev Idx : ℕ := 6
@[inherit_doc Len] abbrev Rem : ℕ := 7

end Resid

open Resid in
/-- resid(len, s, sg, M, key, fr): for i < len, mem[key + i] := emod(sg * mem[s + i], M, fr). -/
def residBody (pEmod : ℕ) : Stmt :=
  .for Idx (v Len) (
    .call pEmod [v Sign *' M (v Src +' v Idx), v Modulus, v Free] Rem ;;
    .store (v Key +' v Idx) (v Rem))

/-- What is allowed for resid covers what emod needs one level of calls further down. -/
theorem emodNeed_ok {len V Mo fr d : ℕ} (h : (residNeed len V Mo).Ok lim fr d) :
    (emodNeed V Mo).Ok lim fr (d + 1) := by
  refine h.mono ?_ le_rfl le_rfl
  have hlen : 1 ≤ (len + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  -- 4 V + 4 M + 16 ≤ 64 (M + 1) (V + 1) ≤ 64 (len + 1)² (M + 1) (V + 1)
  calc 4 * V + 4 * Mo + 16 ≤ 64 * 1 * (Mo + 1) * (V + 1) := by nlinarith [Nat.zero_le (V * Mo)]
    _ ≤ 64 * (len + 1) ^ 2 * (Mo + 1) * (V + 1) := by gcongr

/-- The memory before round i of resid: the first i remainders are written, and below the free
pointer no cell outside the len cells from key has changed. -/
def ResidInv (μ : ℕ → ℤ) (fr key Mo : ℕ) (sg : ℤ) (L : List ℤ) (i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ j (hj : j < L.length), j < i → μ' (key + j) = (sg * L[j]) % (Mo : ℤ)) ∧
    KeptBut μ μ' fr key L.length

/-- A round of resid: emod has changed no cell below the free pointer, and remainder number i is
written. -/
theorem ResidInv.succ {μ μ' μ'' : ℕ → ℤ} {fr key Mo i : ℕ} {sg : ℤ} {L : List ℤ}
    (h : ResidInv μ fr key Mo sg L i μ') (hi : i < L.length) (hkey : key + L.length ≤ fr)
    (hkept : Kept μ' μ'' fr) :
    ResidInv μ fr key Mo sg L (i + 1)
      (Function.update μ'' (key + i) ((sg * L[i]) % (Mo : ℤ))) := by
  refine ⟨fun j hj hji => ?_, (h.2.then hkept fun b hb => ⟨hb, hb.1⟩).write (by omega) _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hji with hji | rfl
  · rw [Function.update_of_ne (by omega), hkept _ (by omega), h.1 j hj hji]
  · exact Function.update_self ..

/-- **resid** meets its specification. -/
theorem resid_spec {p pEmod : ℕ} (hP : P[p]? = some (residBody pEmod))
    (hEmod : EmodSpec lim P pEmod) : ResidSpec lim P p := by
  intro d fr V Mo s key sg L μ hM hsg hL hseg hs hkey hap hok
  refine ⟨_, hP, ?_⟩
  have := hok.space
  have := hok.cells
  have hdepth := hok.depth
  have hword := (emodNeed_ok hok).word
  simp only [residNeed, emodNeed] at hword hdepth
  -- for i < len; the local Rem holds anything
  refine Ends.forShape (fun i (r : ℤ) μ' => ⟨frame [L.length, s, sg, Mo, key, fr, i, r], μ'⟩)
    (ResidInv μ fr key Mo sg L) L.length (tEmod V + 15) 0
    ⟨fun j _ hj => absurd hj (by omega), .refl⟩ ?round ?done
    (first := by rw [update_frame_setLocal, ← frame_append_zeros _ 1]; rfl)
    (hT := by simp [tResid]; ring_nf; omega)
  case round =>
    intro i r μ' hi inv
    -- The number is still in its cell, and its product with the sign is at most V in absolute
    -- value; habs: |sg * x| = |sg| * |x|.
    have hread : μ' (s + i) = L[i] := by
      rw [inv.2 _ (by omega), hseg i hi]
    have hprod : |sg * L[i]| ≤ (V : ℤ) := by
      rcases hsg with rfl | rfl <;> simpa using hL.getElem hi
    have := abs_mul sg L[i]
    -- r := emod(sg * mem[s + i], M, fr)
    refine Ends.callToThen (hEmod (d + 1) fr V Mo (sg * L[i]) μ' hM hprod (emodNeed_ok hok)) ?_
      (by simp [Limits.Addr, abs_le, hread]; omega)
    rintro _ μ'' ⟨rfl, hkept⟩
    -- mem[key + i] := r
    light_store (key + i) ((sg * L[i]) % (Mo : ℤ))
    exact ⟨_, _, rfl, inv.succ hi hkey hkept⟩
  case done =>
    rintro r μ' ⟨written, kept⟩
    exact ⟨fun j hj => (written j (by simpa using hj) (by simpa using hj)).trans (by simp), kept⟩

/-! ## tally -/

namespace Tally

/-- The local variables of tally: the arguments len, key, cnt, δ, and the counter i. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Key : ℕ := 1
@[inherit_doc Len] abbrev Count : ℕ := 2
@[inherit_doc Len] abbrev Delta : ℕ := 3
@[inherit_doc Len] abbrev Idx : ℕ := 4

end Tally

open Tally in
/-- tally(len, key, cnt, δ): for i < len, mem[cnt + mem[key + i]] += δ. -/
def tallyBody : Stmt :=
  .for Idx (v Len) (
    .store (v Count +' M (v Key +' v Idx)) (M (v Count +' M (v Key +' v Idx)) +' v Delta))

/-- The memory before round i of tally: the first i keys have been counted, and no cell outside the
count table has changed. -/
def TallyInv (μ : ℕ → ℤ) (cnt cap : ℕ) (δ : ℤ) (K : List ℕ) (i : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ r < cap, μ' (cnt + r) = μ (cnt + r) + δ * ((K.take i).count r : ℤ)) ∧ SameOutside μ μ' cnt cap

/-- A round of tally counts the key number i. -/
theorem TallyInv.succ {μ μ' : ℕ → ℤ} {cnt cap i : ℕ} {δ : ℤ} {K : List ℕ}
    (h : TallyInv μ cnt cap δ K i μ') (hi : i < K.length) (hk : K[i] < cap) :
    TallyInv μ cnt cap δ K (i + 1) (Function.update μ' (cnt + K[i]) (μ' (cnt + K[i]) + δ)) := by
  refine ⟨fun r hr => ?_, h.2.write (by omega) _⟩
  rw [List.count_take_succ K r hi]
  by_cases hrk : K[i] = r
  · subst hrk
    rw [Function.update_self, h.1 _ hk, if_pos rfl]
    push_cast
    ring
  · rw [Function.update_of_ne (by omega), h.1 r hr, if_neg hrk, Nat.add_zero]

/-- **tally** meets its specification. -/
theorem tally_spec {p : ℕ} (hP : P[p]? = some tallyBody) : TallySpec lim P p := by
  intro d key cnt cap δ K μ hK hδ hseg hap hbd hkey hcnt hw hword
  refine ⟨_, hP, ?_⟩
  -- for i < len
  refine Ends.forFrame (TallyInv μ cnt cap δ K) K.length ⟨fun r _ => by simp, .refl⟩
    ?round ?done (hT := by simp [tTally]; omega)
  case round =>
    intro i μ' hi inv
    have hk : K[i] < cap := hK _ (List.getElem_mem hi)
    -- The key is still in its cell, and the count that is changed is at most len + i in absolute
    -- value.
    have hread : μ' (key + i) = (K[i] : ℕ) := by
      rw [inv.2 _ (by omega), SegN.getElem hseg hi]
    have : (K.take i).count K[i] ≤ i := List.count_le_length.trans (by simp)
    have := inv.1 _ hk
    have := abs_le.1 (hbd _ hk)
    -- mem[cnt + mem[key + i]] += δ
    refine Ends.storeTo (cnt + K[i]) (μ' (cnt + K[i]) + δ) ⟨rfl, inv.succ hi hk⟩ ?_
    rcases hδ with rfl | rfl <;> simp [Limits.Addr, abs_le, hread] <;> omega
  case done =>
    exact fun μ' inv => ⟨fun r hr => (inv.1 r hr).trans (by rw [List.take_length]), inv.2⟩

/-! ## The pure side: buckets, collisions and heavy elements from the list of the remainders -/

/-- The number of colliding pairs, from the list of the remainders. -/
theorem coll_eq_list {L : List ℤ} (hL : L.Nodup) {Mo : ℕ} (hM : 1 ≤ Mo) :
    (coll L.toFinset Mo : ℤ)
      = ((keys Mo L).map fun q => ((keys Mo L).count q : ℤ) - 1).sum := by
  rw [coll_eq_sum, List.sum_toFinset _ hL]
  have h : ∀ x ∈ L, ((#(bucket L.toFinset Mo (x % (Mo : ℤ))) - 1 : ℕ) : ℤ)
      = ((keys Mo L).count (x % (Mo : ℤ)).toNat : ℤ) - 1 := by
    intro x hx
    rw [← Int.natCast_toNat_emod hM x, card_bucket hM hL]
    have : 1 ≤ (keys Mo L).count (x % (Mo : ℤ)).toNat :=
      List.count_pos_iff.2 (List.mem_map.2 ⟨x, hx, rfl⟩)
    rw [Int.natCast_toNat_emod hM x]
    omega
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

/-- Between the two calls of tally: the remainders stand at the free pointer, and the table holds
how often each of them occurs. -/
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
  exact le_trans (by exact_mod_cast hle) h

/-- A table that held zeros and holds zeros again has not changed. -/
theorem sameOn_of_zeroAt {R : ℕ → Prop} {μ μ' : ℕ → ℤ} {cnt cap : ℕ}
    (h : SameOn (fun b => R b ∧ Outside cnt cap b) μ μ') (hz : ZeroAt μ cnt cap)
    (hz' : ZeroAt μ' cnt cap) : SameOn R μ μ' := fun b hb => by
  by_cases hin : Outside cnt cap b
  · exact h b ⟨hb, hin⟩
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

variable {μ μ₁ : ℕ → ℤ} {d fr V Mo s cnt cap pResid pTally : ℕ} {L : List ℤ} {K : List ℕ}

/-- resid(len, s, sg, M, fr, fr + len) writes the remainders of the numbers sg · x to the free
pointer. -/
theorem resid_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hResid : ResidSpec lim P pResid)
    {sg : ℤ} (hsg : sg = 1 ∨ sg = -1) :
    Meets lim P pResid (d + 1) [L.length, s, sg, Mo, fr, (fr + L.length : ℕ)] μ (tResid L.length V)
      fun _ μ₁ => SegN μ₁ fr (keys Mo (L.map (sg * ·))) ∧ Kept μ μ₁ fr := by
  have hlist := C.belowList
  refine (hResid (d + 1) (fr + L.length) V Mo s fr sg L μ C.modulus_pos hsg C.bounded C.list
    (by omega) le_rfl (Or.inl hlist) (C.ok.mono le_rfl ?_ ?_)).mono le_rfl ?_
  · simp only [residNeed, collNeed]
    omega
  · simp only [residNeed, collNeed]
    omega
  · rintro _ μ₁ ⟨written, kept⟩
    refine ⟨?_, kept.mono fun b hb => ⟨by omega, Or.inl hb⟩⟩
    rwa [SegN, map_cast_keys C.modulus_pos, List.map_map]

/-- resid(len, s, 1, M, fr, fr + len) writes the remainders of the numbers of L to the free
pointer. -/
theorem keys_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hResid : ResidSpec lim P pResid) :
    Meets lim P pResid (d + 1) [L.length, s, 1, Mo, fr, (fr + L.length : ℕ)] μ (tResid L.length V)
      fun _ μ₁ => SegN μ₁ fr (keys Mo L) ∧ Kept μ μ₁ fr := by
  simpa using C.resid_meets hResid (Or.inl rfl)

/-- tally(len, fr, cnt, δ), run on the remainders K at the free pointer, adds δ times the number of
occurrences of q in K to cell q of the table.  Of the hypotheses of `TallySpec` only the bound on
the table is left. -/
theorem tally_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hTally : TallySpec lim P pTally)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < Mo) {δ : ℤ} (hδ : δ = 1 ∨ δ = -1)
    (hkeys : SegN μ₁ fr K) (hbd : ∀ q < cap, |μ₁ (cnt + q)| ≤ (L.length : ℤ)) :
    Meets lim P pTally (d + 1) [L.length, fr, cnt, δ] μ₁ (tTally L.length) fun _ μ₂ =>
      (∀ q < cap, μ₂ (cnt + q) = μ₁ (cnt + q) + δ * (K.count q : ℤ)) ∧
        SameOutside μ₁ μ₂ cnt cap := by
  have hcells := C.ok.cells
  have htable := C.belowTable
  have := sq_add_le_word C.ok.word
  have : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  simp only [collNeed] at hcells
  have h := hTally (d + 1) fr cnt cap δ K μ₁ (fun q hq => (hlt q hq).trans_le C.modulus_le) hδ hkeys
    (Or.inr htable)
  rw [hlen] at h
  exact h hbd (by omega) (by omega) C.ok.space (by omega)

/-- tally(len, fr, cnt, 1) counts the remainders. -/
theorem count_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hTally : TallySpec lim P pTally)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < Mo) (hkeys : SegN μ₁ fr K)
    (kept : Kept μ μ₁ fr) :
    Meets lim P pTally (d + 1) [L.length, fr, cnt, 1] μ₁ (tTally L.length) fun _ μ₂ =>
      Counted μ₂ fr cnt cap K ∧ KeptBut μ μ₂ fr cnt cap := by
  have htable := C.belowTable
  have hzero : ZeroAt μ₁ cnt cap := fun q hq => (kept _ (by omega)).trans (C.zero q hq)
  refine (C.tally_meets hTally hlen hlt (Or.inl rfl) hkeys fun q hq => by simp [hzero q hq]).mono
    le_rfl ?_
  rintro _ μ₂ ⟨counts, same⟩
  exact ⟨⟨hkeys.of_sameOutside same (Or.inr htable),
    fun q hq => by rw [counts q hq, hzero q hq]; ring⟩, kept.then same fun b hb => hb⟩

/-- tally(len, fr, cnt, -1) removes the remainders from the table. -/
theorem uncount_meets (C : BucketPre lim μ d fr V Mo s cnt cap L) (hTally : TallySpec lim P pTally)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < Mo) (h : Counted μ₁ fr cnt cap K) :
    Meets lim P pTally (d + 1) [L.length, fr, cnt, -1] μ₁ (tTally L.length) fun _ μ₂ =>
      ZeroAt μ₂ cnt cap ∧ SameOutside μ₁ μ₂ cnt cap := by
  refine (C.tally_meets hTally hlen hlt (Or.inr rfl) h.keys fun q hq => ?_).mono le_rfl ?_
  · rw [h.counts q hq, abs_of_nonneg (by positivity), ← hlen]
    exact_mod_cast List.count_le_length
  · rintro _ μ₂ ⟨counts, same⟩
    exact ⟨fun q hq => by rw [counts q hq, h.counts q hq]; ring, same⟩

end BucketPre

/-! ## coll -/

namespace Coll

/-- The local variables of coll: the arguments len, s, M, cnt, fr, the results of the calls, which
are not used, the counter i, and the sum.  Local 0 also takes the result. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Result : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Modulus : ℕ := 2
@[inherit_doc Len] abbrev Count : ℕ := 3
@[inherit_doc Len] abbrev Free : ℕ := 4
@[inherit_doc Len] abbrev Res : ℕ := 5
@[inherit_doc Len] abbrev Idx : ℕ := 6
@[inherit_doc Len] abbrev Total : ℕ := 7

end Coll

open Coll in
/-- The part of coll that adds up: sum := 0; for i < len, sum += mem[cnt + mem[fr + i]] - 1. -/
def collSum : Stmt :=
  .set Total (k 0) ;;
  .for Idx (v Len) (.set Total (v Total +' M (v Count +' M (v Free +' v Idx)) -' k 1))

open Coll in
/-- coll(len, s, M, cnt, fr) writes the remainders to fr, counts them, adds up, removes them from
the table, and returns the sum. -/
def collBody (pResid pTally : ℕ) : Stmt :=
  .call pResid [v Len, v Src, k 1, v Modulus, v Free, v Free +' v Len] Res ;;
  .call pTally [v Len, v Free, v Count, k 1] Res ;;
  collSum ;;
  .call pTally [v Len, v Free, v Count, k 0 -' k 1] Res ;;
  .set Result (v Total)

/-- The sum over the first `i` remainders. -/
def collPart (K : List ℕ) (i : ℕ) : ℤ := ((K.take i).map fun q => (K.count q : ℤ) - 1).sum

/-- The sum over the first i + 1 remainders is that over the first i, plus the term of remainder
i. -/
theorem collPart_succ (K : List ℕ) {i : ℕ} (hi : i < K.length) :
    collPart K (i + 1) = collPart K i + ((K.count K[i] : ℤ) - 1) := by
  unfold collPart
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.map_append, List.sum_append]
  simp

/-- The sum over the first `i` remainders lies between 0 and `i` times the number of remainders. -/
theorem collPart_bounds (K : List ℕ) :
    ∀ i, i ≤ K.length → 0 ≤ collPart K i ∧ collPart K i ≤ (i : ℤ) * (K.length : ℤ) := by
  intro i
  induction i with
  | zero => intro _; simp [collPart]
  | succ i ih =>
    intro hi
    obtain ⟨hlow, hhigh⟩ := ih (by omega)
    have : 1 ≤ K.count K[i] := List.count_pos_iff.2 (List.getElem_mem _)
    have : K.count K[i] ≤ K.length := List.count_le_length
    rw [collPart_succ K (by omega)]
    push_cast
    exact ⟨by omega, by nlinarith⟩

/-- **The loop of coll** leaves the sum over all remainders in the local Total and writes no
cell. -/
theorem collSum_ends {d V s Mo cnt cap fr : ℕ} {r : ℤ} {μ₀ μ : ℕ → ℤ} {L : List ℤ}
    (C : BucketPre lim μ₀ d fr V Mo s cnt cap L) (counted : Counted μ fr cnt cap (keys Mo L)) :
    Ends lim P d collSum ⟨frame [L.length, s, Mo, cnt, fr, r], μ⟩ (20 * L.length + 10) fun σ' =>
      σ' = ⟨frame [L.length, s, Mo, cnt, fr, r, L.length, collPart (keys Mo L) L.length], μ⟩ := by
  have := C.ok.space
  have := sq_add_le_word C.ok.word
  have hcells := C.ok.cells
  have := C.belowTable
  simp only [collNeed] at hcells
  have hn := length_keys Mo L
  have hK : ∀ q ∈ keys Mo L, q < cap := fun q hq =>
    (keys_lt C.modulus_pos _ q hq).trans_le C.modulus_le
  clear C
  generalize keys Mo L = K at *
  generalize L.length = n at *
  have : (0 : ℤ) ≤ (n : ℤ) * n := by positivity
  -- sum := 0
  light_set 0
  -- for i < len
  refine Ends.for (fun i σ => σ = ⟨frame [n, s, Mo, cnt, fr, r, i, collPart K i], μ⟩) n 12
    ?start ?round ?done ?bound
  case start => simp [update_frame_setLocal, collPart]
  case done => exact fun _ _ hσ => hσ
  case bound =>
    rintro i _ - - rfl
    simp
  case round =>
    rintro i _ hi - rfl
    have hiK : i < K.length := by omega
    have hq : K[i] < cap := hK _ (List.getElem_mem hiK)
    -- The two cells that the round reads, and the bounds on the old and the new sum.
    have hkey : μ (fr + i) = (K[i] : ℕ) := counted.keys.getElem hiK
    have hcount := counted.counts _ hq
    have : 1 ≤ K.count K[i] := List.count_pos_iff.2 (List.getElem_mem _)
    have : K.count K[i] ≤ n := hn ▸ List.count_le_length
    obtain ⟨hlow, hhigh⟩ := collPart_bounds K i hiK.le
    have : collPart K i ≤ (n : ℤ) * n :=
      hhigh.trans (hn ▸ mul_le_mul_of_nonneg_right (by exact_mod_cast hiK.le) (by positivity))
    -- sum += mem[cnt + mem[fr + i]] - 1
    refine Ends.setTo (collPart K (i + 1)) ⟨by simp, by rw [update_frame_setLocal]; rfl⟩ ?_
    rw [collPart_succ K hiK]
    simp [Limits.Addr, abs_le, hkey, hcount]
    omega

/-- **coll** meets its specification. -/
theorem coll_spec {p pResid pTally : ℕ} (hP : P[p]? = some (collBody pResid pTally))
    (hResid : ResidSpec lim P pResid) (hTally : TallySpec lim P pTally) : CollSpec lim P p := by
  intro d fr V Mo s len cnt cap S μ hmem hok
  obtain ⟨L, rfl, hnd, rfl, C⟩ := hmem.exists_pre hok
  refine ⟨_, hP, ?_⟩
  have hM := C.modulus_pos
  have := hok.space
  have := sq_add_le_word hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  have : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  simp only [collNeed] at hcells hdepth
  -- resid(len, s, 1, M, fr, fr + len)
  light_call (C.keys_meets hResid) using tColl with _ μ₁ ⟨hkeys, kept₁⟩
  -- tally(len, fr, cnt, 1)
  light_call (C.count_meets hTally (length_keys Mo L) (keys_lt hM L) hkeys kept₁)
    using tColl with r μ₂ ⟨counted, kept₂⟩
  -- the sum
  light_piece (collSum_ends C counted) using tColl with _ rfl
  -- tally(len, fr, cnt, -1)
  light_call (C.uncount_meets hTally (length_keys Mo L) (keys_lt hM L) counted)
    using tColl with _ μ₃ ⟨zero₃, same₃⟩
  -- return the sum
  refine Ends.setTo (coll L.toFinset Mo : ℤ)
    ⟨by simp, sameOn_of_zeroAt (kept₂.then same₃ fun b hb => ⟨hb, hb.2⟩) C.zero zero₃⟩ ?_
    (by simp [tColl]; omega)
  rw [coll_eq_list hnd hM, collPart, ← length_keys Mo L, List.take_length]
  simp

/-! ## heavy -/

namespace Heavy

/-- The local variables of heavy: the arguments len, s, M, out, cnt, fr, the results of the calls,
which are not used, the counter i, and the number j of elements written.  Local 0 also takes the
result. -/
abbrev Len : ℕ := 0
@[inherit_doc Len] abbrev Result : ℕ := 0
@[inherit_doc Len] abbrev Src : ℕ := 1
@[inherit_doc Len] abbrev Modulus : ℕ := 2
@[inherit_doc Len] abbrev Out : ℕ := 3
@[inherit_doc Len] abbrev Count : ℕ := 4
@[inherit_doc Len] abbrev Free : ℕ := 5
@[inherit_doc Len] abbrev Res : ℕ := 6
@[inherit_doc Len] abbrev Idx : ℕ := 7
@[inherit_doc Len] abbrev Written : ℕ := 8

end Heavy

open Heavy in
/-- A round of the loop of heavy: if 1 < mem[cnt + mem[fr + i]] then mem[out + j] := mem[s + i] and
j := j + 1. -/
def heavyRound : Stmt :=
  .ite (k 1 <' M (v Count +' M (v Free +' v Idx)))
    (.store (v Out +' v Written) (M (v Src +' v Idx)) ;; .set Written (v Written +' k 1)) .skip

open Heavy in
/-- The part of heavy that copies: j := 0; a round for each i < len. -/
def heavyCopy : Stmt :=
  .set Written (k 0) ;;
  .for Idx (v Len) heavyRound

open Heavy in
/-- heavy(len, s, M, out, cnt, fr) writes the remainders to fr, counts them, copies the heavy
elements, removes the remainders from the table, and returns the number of heavy elements. -/
def heavyBody (pResid pTally : ℕ) : Stmt :=
  .call pResid [v Len, v Src, k 1, v Modulus, v Free, v Free +' v Len] Res ;;
  .call pTally [v Len, v Free, v Count, k 1] Res ;;
  heavyCopy ;;
  .call pTally [v Len, v Free, v Count, k 0 -' k 1] Res ;;
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

/-- The state before round i of the loop of heavy: the heavy elements among the first i elements
are written, and no cell outside the output has changed. -/
def HeavyInv (μ : ℕ → ℤ) (s Mo out cnt fr : ℕ) (r : ℤ) (L : List ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ μ' : ℕ → ℤ,
    σ = ⟨frame [L.length, s, Mo, out, cnt, fr, r, i, (heavyPart Mo L i).length], μ'⟩ ∧
      Seg μ' out (heavyPart Mo L i) ∧ SameOutside μ μ' out L.length

/-- **A round of the loop of heavy** copies element i if it is heavy.  μ₀ is the memory at the start
of heavy (of C only the layout and the limits are used), μ the memory at the start of the loop.  The
conclusion has the form that `Ends.for` asks of a round. -/
theorem heavyRound_ends {d V s Mo out cnt cap fr i : ℕ} {r : ℤ} {μ₀ μ : ℕ → ℤ} {L : List ℤ}
    (C : BucketPre lim μ₀ d fr V Mo s cnt cap L) (counted : Counted μ fr cnt cap (keys Mo L))
    (hL : Seg μ s L) (O : HeavyOut fr s cnt cap out L.length) (hi : i < L.length) {σ : State}
    (hσ : HeavyInv μ s Mo out cnt fr r L i σ) :
    Ends lim P d heavyRound σ 22 fun σ' => σ'.loc Heavy.Idx = i ∧
      HeavyInv μ s Mo out cnt fr r L (i + 1)
        { σ' with loc := Function.update σ'.loc Heavy.Idx ((i : ℤ) + 1) } := by
  obtain ⟨μ', rfl, written, same⟩ := hσ
  have hcells := C.ok.cells
  light_facts C O C.ok
  simp only [collNeed] at hcells
  have hiK : i < (keys Mo L).length := by rwa [length_keys]
  have : (keys Mo L)[i] < Mo := keys_lt C.modulus_pos _ _ (List.getElem_mem hiK)
  have hqi : (keys Mo L)[i] = (L[i] % (Mo : ℤ)).toNat := by simp [keys]
  -- The three cells that the round reads have not changed.
  have hkey : μ' (fr + i) = ((keys Mo L)[i] : ℕ) :=
    (same _ (Or.inr (by omega))).trans (counted.keys.getElem hiK)
  have hcount : μ' (cnt + (keys Mo L)[i]) = ((keys Mo L).count (keys Mo L)[i] : ℤ) :=
    (same _ (by omega)).trans (counted.counts _ (by omega))
  have hread : μ' (s + i) = L[i] := (same _ (by omega)).trans (hL i hi)
  have : (heavyPart Mo L i).length ≤ i := Spec.length_passList_le _ _ _ _
  -- if 1 < mem[cnt + mem[fr + i]]
  refine Ends.iteLast (fun hheavy => ?_) (fun hlight => ?_)
    (by light_side [hkey])
  · have htwo : 2 ≤ (keys Mo L).count (keys Mo L)[i] :=
      Nat.succ_le_of_lt (by simpa [hkey, hcount] using hheavy)
    have hsucc : heavyPart Mo L (i + 1) = heavyPart Mo L i ++ [L[i]] :=
      Spec.passList_succ_of id hi (by simpa [isHeavy, ← hqi] using htwo)
    -- mem[out + j] := mem[s + i]
    light_store (out + (heavyPart Mo L i).length) L[i] using hread
    -- j := j + 1
    light_set ((heavyPart Mo L (i + 1)).length : ℤ) using hsucc
    exact ⟨by simp, Function.update μ' (out + (heavyPart Mo L i).length) L[i],
        by rw [update_frame_setLocal]; rfl, hsucc ▸ written.snoc _,
        same.update ⟨by omega, by omega⟩ _⟩
  · have hnottwo : ¬ 2 ≤ (keys Mo L).count (keys Mo L)[i] := fun htwo =>
      hlight (by simpa [hkey, hcount] using Nat.lt_of_succ_le htwo)
    have hsucc : heavyPart Mo L (i + 1) = heavyPart Mo L i :=
      Spec.passList_succ_of_not id hi (by simpa [isHeavy, ← hqi] using hnottwo)
    exact Ends.skip
      ⟨by simp, μ', by rw [update_frame_setLocal, hsucc]; rfl, hsucc ▸ written, same⟩

/-- **The loop of heavy** writes the heavy elements and leaves their number in the local Written. -/
theorem heavyCopy_ends {d V s Mo out cnt cap fr : ℕ} {r : ℤ} {μ₀ μ : ℕ → ℤ} {L : List ℤ}
    (C : BucketPre lim μ₀ d fr V Mo s cnt cap L) (counted : Counted μ fr cnt cap (keys Mo L))
    (hL : Seg μ s L) (O : HeavyOut fr s cnt cap out L.length) :
    Ends lim P d heavyCopy ⟨frame [L.length, s, Mo, out, cnt, fr, r], μ⟩ (30 * L.length + 10)
      (HeavyInv μ s Mo out cnt fr r L L.length) := by
  have := sq_add_le_word C.ok.word
  have : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  -- j := 0
  light_set 0
  -- for i < len
  refine Ends.for (HeavyInv μ s Mo out cnt fr r L) L.length 22 ?start ?round ?done ?bound
  case start => exact ⟨μ, by simp [update_frame_setLocal], by simp, .refl⟩
  case round => exact fun i σ hi _ hσ => heavyRound_ends C counted hL O hi hσ
  case done => exact fun _ _ hσ => hσ
  case bound =>
    rintro i _ - - ⟨μ', rfl, -⟩
    simp

/-- **heavy** meets its specification. -/
theorem heavy_spec {p pResid pTally : ℕ} (hP : P[p]? = some (heavyBody pResid pTally))
    (hResid : ResidSpec lim P pResid) (hTally : TallySpec lim P pTally) : HeavySpec lim P p := by
  intro d fr V Mo s len out cnt cap S μ hmem O hok
  obtain ⟨L, rfl, hnd, rfl, C⟩ := hmem.exists_pre hok
  refine ⟨_, hP, ?_⟩
  have hout := O.below
  have hapc := O.apartTable
  have hM := C.modulus_pos
  light_facts C hok
  have := sq_add_le_word hok.word
  have hcells := hok.cells
  have hdepth := hok.depth
  have : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  simp only [collNeed] at hcells hdepth
  -- resid(len, s, 1, M, fr, fr + len)
  light_call (C.keys_meets hResid) using tHeavy with _ μ₁ ⟨hkeys, kept₁⟩
  -- tally(len, fr, cnt, 1)
  light_call (C.count_meets hTally (length_keys Mo L) (keys_lt hM L) hkeys kept₁)
    using tHeavy with r μ₂ ⟨counted, kept₂⟩
  have hseg₂ : Seg μ₂ s L := C.list.keep
  -- the heavy elements are copied
  light_piece (heavyCopy_ends C counted hseg₂ O) using tHeavy with _ ⟨μ₃, rfl, written, same₃⟩
  rw [heavyPart_length] at written
  -- tally(len, fr, cnt, -1)
  light_call (C.uncount_meets hTally (length_keys Mo L) (keys_lt hM L)
    (counted.of_sameOutside same₃ hout hapc)) using tHeavy with _ μ₄ ⟨zero₄, same₄⟩
  have hnd' : (heavyList Mo L).Nodup := hnd.filter _
  have hcard : #(heavy L.toFinset Mo) = (heavyList Mo L).length := by
    rw [← heavyList_toFinset hnd hM, List.toFinset_card_of_nodup hnd']
  have : (heavyList Mo L).length ≤ L.length := List.length_filter_le _ _
  -- return the number of heavy elements
  refine Ends.setTo (#(heavy L.toFinset Mo) : ℤ) ⟨by simp,
    ⟨heavyList Mo L, hcard.symm, written.keep,
      hnd', heavyList_toFinset hnd hM⟩, ?_⟩ (by simp [hcard, heavyPart_length])
    (by simp [tHeavy]; omega)
  exact sameOn_of_zeroAt ((kept₂.then same₃ fun b hb => ⟨⟨hb.1.1, hb.2⟩, hb.1.2⟩).then same₄
    fun b hb => ⟨hb, hb.2⟩) C.zero zero₄

end Light.Sec3.ChanHe
end

section
namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec.ChanHeArray

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The local variables -/

namespace ArrLocals

/-- The local variables of nodeArray: the arguments M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr; the
numbers W and G; a counter, an address, a remainder, a value and the result of a call, which the
padding loop and the passes use; the number 2m² of groups; the parameters of a pass, which are the
sign sg, the number g that is added, the address and the length of the set, the number of the cell
in its group, and the distance to the second cell; the free pointer behind the remainders; and the
padding pattern. -/
abbrev MOD : ℕ := 0
@[inherit_doc MOD] abbrev SET1 : ℕ := 1
@[inherit_doc MOD] abbrev LEN1 : ℕ := 2
@[inherit_doc MOD] abbrev SET2 : ℕ := 3
@[inherit_doc MOD] abbrev LEN2 : ℕ := 4
@[inherit_doc MOD] abbrev SET3 : ℕ := 5
@[inherit_doc MOD] abbrev LEN3 : ℕ := 6
@[inherit_doc MOD] abbrev VMAX : ℕ := 7
@[inherit_doc MOD] abbrev MMAX : ℕ := 8
@[inherit_doc MOD] abbrev ARRAY : ℕ := 9
@[inherit_doc MOD] abbrev CNT : ℕ := 10
@[inherit_doc MOD] abbrev FREE : ℕ := 11
@[inherit_doc MOD] abbrev WIDTH : ℕ := 12
@[inherit_doc MOD] abbrev GAP : ℕ := 13
@[inherit_doc MOD] abbrev IDX : ℕ := 14
@[inherit_doc MOD] abbrev ADDR : ℕ := 15
@[inherit_doc MOD] abbrev KEY : ℕ := 16
@[inherit_doc MOD] abbrev VAL : ℕ := 17
@[inherit_doc MOD] abbrev RES : ℕ := 18
@[inherit_doc MOD] abbrev GROUPS : ℕ := 19
@[inherit_doc MOD] abbrev SIGN : ℕ := 20
@[inherit_doc MOD] abbrev SHIFT : ℕ := 21
@[inherit_doc MOD] abbrev SRC : ℕ := 22
@[inherit_doc MOD] abbrev LEN : ℕ := 23
@[inherit_doc MOD] abbrev OFF : ℕ := 24
@[inherit_doc MOD] abbrev DIST : ℕ := 25
@[inherit_doc MOD] abbrev FR2 : ℕ := 26
@[inherit_doc MOD] abbrev PAD0 : ℕ := 27
@[inherit_doc MOD] abbrev PAD1 : ℕ := 28
@[inherit_doc MOD] abbrev PAD2 : ℕ := 29
@[inherit_doc MOD] abbrev PAD3 : ℕ := 30

end ArrLocals

/-- The arguments of nodeArray. -/
structure ArrArgs : Type where
  Mo : ℕ
  s₁ : ℕ
  l₁ : ℕ
  s₂ : ℕ
  l₂ : ℕ
  s₃ : ℕ
  l₃ : ℕ
  V : ℕ
  m : ℕ
  y : ℕ
  cnt : ℕ
  fr : ℕ

/-- The padding pattern: what cell t of a group holds before the passes. -/
def padVal (V : ℕ) (t : ℕ) : ℤ :=
  if t = 0 then 10 * (6 * V + 4) else if t = 1 then (2 * V + 1) + (6 * V + 4)
  else if t = 2 then (2 * V + 1) + 3 * (6 * V + 4) else -(2 * V + 1) + 4 * (6 * V + 4)

/-- The scratch variables of the padding loop and of a pass: counter, address, remainder, value,
result of a call, and the free pointer behind the remainders. -/
structure ArrScratch : Type where
  idx : ℤ
  ad : ℤ
  key : ℤ
  val : ℤ
  res : ℤ
  fr2 : ℤ

/-- The list of the local variables of nodeArray, once the constants have been computed. -/
abbrev arrLocals (a : ArrArgs) (x : ArrScratch) (sg g : ℤ) (s len off δ : ℕ) : List ℤ :=
  [a.Mo, a.s₁, a.l₁, a.s₂, a.l₂, a.s₃, a.l₃, a.V, a.m, a.y, a.cnt, a.fr, 2 * a.V + 1, 6 * a.V + 4,
    x.idx, x.ad, x.key, x.val, x.res, (2 * (a.m * a.m) : ℕ), sg, g, s, len, off, δ, x.fr2,
    padVal a.V 0, padVal a.V 1, padVal a.V 2, padVal a.V 3]

/-! ## The padding pattern -/

open ArrLocals in
/-- For i < 2m²: the four cells of group i become the padding pattern. -/
def padStmt : Stmt :=
  .for IDX (v GROUPS) (
    .store (v ARRAY +' k 4 *' v IDX) (v PAD0) ;;
    .store (v ARRAY +' k 4 *' v IDX +' k 1) (v PAD1) ;;
    .store (v ARRAY +' k 4 *' v IDX +' k 2) (v PAD2) ;;
    .store (v ARRAY +' k 4 *' v IDX +' k 3) (v PAD3))

/-- The memory before group j is written: the groups below j hold the pattern p, and no cell outside
the c groups has changed. -/
def PadInv (μ : ℕ → ℤ) (y c : ℕ) (p : ℕ → ℤ) (j : ℕ) (μ' : ℕ → ℤ) : Prop :=
  (∀ i < j, ∀ t < 4, μ' (y + 4 * i + t) = p t) ∧ SameOutside μ μ' y (4 * c)

/-- One more group. -/
theorem PadInv.succ {μ μ' : ℕ → ℤ} {y c j : ℕ} {p : ℕ → ℤ} (h : PadInv μ y c p j μ') (hj : j < c) :
    PadInv μ y c p (j + 1) (Function.update (Function.update (Function.update (Function.update μ'
      (y + 4 * j) (p 0)) (y + 4 * j + 1) (p 1)) (y + 4 * j + 2) (p 2)) (y + 4 * j + 3) (p 3)) := by
  refine ⟨fun i hi t ht => ?_, (((h.2.update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩
    _).update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
  · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega), h.1 i hlt t ht]
  · interval_cases t <;> simp

/-- **The padding pattern** is written to all groups. -/
theorem pad_ends {μ : ℕ → ℤ} {a : ArrArgs} (hw : (lim.space : ℤ) ≤ lim.word)
    (hy : a.y + 4 * (2 * (a.m * a.m)) ≤ lim.space) {x : ArrScratch} {sg g : ℤ}
    {s len off δ : ℕ} :
    Ends lim P d padStmt ⟨frame (arrLocals a x sg g s len off δ), μ⟩ (42 * (2 * (a.m * a.m)) + 6)
      fun σ' => ∃ μ', PadInv μ a.y (2 * (a.m * a.m)) (padVal a.V) (2 * (a.m * a.m)) μ' ∧
        σ' = ⟨frame (arrLocals a { x with idx := (2 * (a.m * a.m) : ℕ) } sg g s len off δ),
          μ'⟩ := by
  -- for i < 2m²
  refine Ends.forFrame (PadInv μ a.y (2 * (a.m * a.m)) (padVal a.V)) (2 * (a.m * a.m))
    ⟨fun i hi => absurd hi (by omega), .refl⟩ ?round ?done
  case round =>
    intro j μ' hj inv
    -- mem[y + 4i] := p₀; mem[y + 4i + 1] := p₁; mem[y + 4i + 2] := p₂; mem[y + 4i + 3] := p₃
    light_store (a.y + 4 * j) (padVal a.V 0)
    light_store (a.y + 4 * j + 1) (padVal a.V 1)
    light_store (a.y + 4 * j + 2) (padVal a.V 2)
    light_store (a.y + 4 * j + 3) (padVal a.V 3)
    exact ⟨rfl, inv.succ hj⟩
  case done => exact fun μ' inv => ⟨μ', inv, rfl⟩

/-! ## One pass over a set -/

open ArrLocals in
/-- A round of the loop of a pass: key := mem[fr + j]; if mem[cnt + key] = 1 then
sg * mem[s + j] + g is written to the cells y + 4 key + off and y + 4 key + off + δ. -/
def placeRound : Stmt :=
  .set KEY (M (v FREE +' v IDX)) ;;
  .ite (M (v CNT +' v KEY) =' k 1)
    (.set ADDR (v ARRAY +' k 4 *' v KEY +' v OFF) ;;
     .set VAL (v SIGN *' M (v SRC +' v IDX) +' v SHIFT) ;;
     .store (v ADDR) (v VAL) ;;
     .store (v ADDR +' v DIST) (v VAL))
    .skip

open ArrLocals in
/-- The loop of a pass: a round for each j < len. -/
def placeLoop : Stmt := .for IDX (v LEN) placeRound

open ArrLocals in
/-- One pass.  The remainders of the numbers sg · x go to the cells from the free pointer and are
counted; the loop writes sg · x + g for every x whose remainder has the count 1; the counts are
removed. -/
def placeStmt (pResid pTally : ℕ) : Stmt :=
  .set FR2 (v FREE +' v LEN) ;;
  .call pResid [v LEN, v SRC, v SIGN, v MOD, v FREE, v FR2] RES ;;
  .call pTally [v LEN, v FREE, v CNT, k 1] RES ;;
  placeLoop ;;
  .call pTally [v LEN, v FREE, v CNT, k 0 -' k 1] RES

/-- The time of a pass over len numbers: remainders, counting, the loop, and removing the counts. -/
def tPlace (len V : ℕ) : ℕ := tResid len V + 2 * tTally len + 45 * len + 32

/-- The cells that a pass may write: the cells y + 4r + off and y + 4r + off + δ for r < M. -/
def PlaceCell (y off δ Mo b : ℕ) : Prop := ∃ r < Mo, b = y + 4 * r + off ∨ b = y + 4 * r + off + δ

/-- The memory μ' before element j of a pass is looked at.  μ is the memory before the loop, K the
list of the remainders, and val r what the cells of the remainder r are to hold.  The cells of the
remainders that have the count 1 and occur among the first j remainders hold their values, and no
other cell has changed. -/
structure PlaceInv (μ μ' : ℕ → ℤ) (y off δ Mo : ℕ) (K : List ℕ) (val : ℕ → ℤ) (j : ℕ) : Prop where
  cells : ∀ r < Mo, ∀ e, (e = 0 ∨ e = δ) → μ' (y + 4 * r + off + e) =
    if K.count r = 1 ∧ r ∈ K.take j then val r else μ (y + 4 * r + off + e)
  rest : SameOn (fun b => ¬ PlaceCell y off δ Mo b) μ μ'

namespace PlaceInv

variable {μ μ' : ℕ → ℤ} {y off δ Mo j : ℕ} {K : List ℕ} {val : ℕ → ℤ}

/-- Before the first element. -/
theorem zero : PlaceInv μ μ y off δ Mo K val 0 := ⟨fun r _ e _ => by simp, .refl⟩

/-- The first j + 1 remainders are the first j and remainder number j. -/
theorem mem_take_succ (hj : j < K.length) (r : ℕ) :
    r ∈ K.take (j + 1) ↔ r ∈ K.take j ∨ r = K[j] := by
  rw [List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton]

/-- An element whose remainder has the count 1 is written to its two cells. -/
theorem succ_one (h : PlaceInv μ μ' y off δ Mo K val j) (hj : j < K.length) (hlt : K[j] < Mo)
    (hone : K.count K[j] = 1) (hδ : δ = 0 ∨ 4 * Mo ≤ δ) :
    PlaceInv μ (Function.update (Function.update μ' (y + 4 * K[j] + off) (val K[j]))
      (y + 4 * K[j] + off + δ) (val K[j])) y off δ Mo K val (j + 1) := by
  refine ⟨fun r hr e he => ?_, fun b hb => ?_⟩
  · by_cases hrK : r = K[j]
    · subst hrK
      rw [if_pos ⟨hone, (mem_take_succ hj _).2 (Or.inr rfl)⟩]
      rcases he with rfl | rfl <;> simp [Function.update_apply]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), h.cells r hr e he]
      simp only [mem_take_succ hj, hrK, or_false]
  · rw [Function.update_of_ne fun hEq => hb ⟨_, hlt, Or.inr hEq⟩,
      Function.update_of_ne fun hEq => hb ⟨_, hlt, Or.inl hEq⟩, h.rest b hb]

/-- An element whose remainder does not have the count 1 is passed over. -/
theorem succ_many (h : PlaceInv μ μ' y off δ Mo K val j) (hj : j < K.length)
    (hmany : K.count K[j] ≠ 1) : PlaceInv μ μ' y off δ Mo K val (j + 1) := by
  refine ⟨fun r hr e he => ?_, h.rest⟩
  rw [h.cells r hr e he]
  by_cases hrK : r = K[j]
  · subst hrK
    simp [hmany]
  · simp only [mem_take_succ hj, hrK, or_false]

/-- After the last element. -/
theorem done (h : PlaceInv μ μ' y off δ Mo K val K.length) {r : ℕ} (hr : r < Mo) {e : ℕ}
    (he : e = 0 ∨ e = δ) : μ' (y + 4 * r + off + e) =
      if K.count r = 1 then val r else μ (y + 4 * r + off + e) := by
  rw [h.cells r hr e he, List.take_length]
  by_cases hone : K.count r = 1
  · rw [if_pos ⟨hone, List.count_pos_iff.1 (by omega)⟩, if_pos hone]
  · rw [if_neg fun h => hone h.1, if_neg hone]

end PlaceInv

/-- What a pass assumes: what coll and heavy assume about the set and the count table; sg is 1
or -1; the array of ylen cells from y lies below the free pointer, apart from the set and the table,
and has room for the cells that the pass writes; off is the number of a cell in its group; the
second cell is the first one (δ = 0) or lies behind the first M groups; and sg · x + g fits in a
word. -/
structure PassPre (lim : Limits) (μ : ℕ → ℤ) (d : ℕ) (a : ArrArgs) (sg g : ℤ) (s off δ cap ylen : ℕ)
    (L : List ℤ) : Prop where
  bucket : BucketPre lim μ d a.fr a.V a.Mo s a.cnt cap L
  sign : sg = 1 ∨ sg = -1
  belowArr : a.y + ylen ≤ a.fr
  apartSet : Apart a.y ylen s L.length
  apartTable : Apart a.y ylen a.cnt cap
  room : 4 * a.Mo + δ ≤ ylen
  off_lt : off < 4
  dist : δ = 0 ∨ 4 * a.Mo ≤ δ
  value_le : |g| + a.V ≤ lim.word

section pass

variable {μ μ₀ : ℕ → ℤ} {a : ArrArgs} {sg g : ℤ} {s off δ cap ylen : ℕ} {L : List ℤ} {K : List ℕ}
  {val : ℕ → ℤ}

/-- A cell that a pass may write lies in the array. -/
theorem PassPre.placeCell_lt (H : PassPre lim μ₀ d a sg g s off δ cap ylen L) {b : ℕ}
    (hb : PlaceCell a.y off δ a.Mo b) : a.y ≤ b ∧ b < a.y + ylen := by
  obtain ⟨r, hr, hb⟩ := hb
  light_facts H
  omega

/-- **A round of the loop of a pass** looks at element j.  μ₀ is the memory at the start of the pass
(of H only the layout and the limits are used), μ the memory at the start of the loop, when the
remainders K have been counted, and μ' the memory before the round. -/
theorem placeRound_ends (H : PassPre lim μ₀ d a sg g s off δ cap ylen L)
    (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < a.Mo) (counted : Counted μ a.fr a.cnt cap K)
    (hL : Seg μ s L) (hval : ∀ j (hK : j < K.length) (hj : j < L.length), K.count K[j] = 1 →
      sg * L[j] + g = val K[j]) (x : ArrScratch) {j : ℕ} (hj : j < L.length) {μ' : ℕ → ℤ}
    (inv : PlaceInv μ μ' a.y off δ a.Mo K val j) :
    Ends lim P d placeRound
      ⟨frame (arrLocals a { x with idx := j } sg g s L.length off δ), μ'⟩ 37 fun σ' =>
      ∃ (x' : ArrScratch) (μ'' : ℕ → ℤ),
        σ' = ⟨frame (arrLocals a { x' with idx := j } sg g s L.length off δ), μ''⟩ ∧
        PlaceInv μ μ'' a.y off δ a.Mo K val (j + 1) := by
  light_facts H H.bucket H.bucket.ok
  have hcells := H.bucket.ok.cells
  simp only [collNeed] at hcells
  have hjK : j < K.length := hlen ▸ hj
  have hkey_lt := hlt _ (List.getElem_mem hjK)
  -- The three cells that the round reads lie outside the array, so they have not changed.
  have hout : ∀ b, (b < a.y ∨ a.y + ylen ≤ b) → μ' b = μ b := fun b hb =>
    inv.rest b fun ⟨r, hr, hEq⟩ => by omega
  have hkey : μ' (a.fr + j) = (K[j] : ℕ) := (hout _ (by omega)).trans (counted.keys.getElem hjK)
  have hcount : μ' (a.cnt + K[j]) = (K.count K[j] : ℤ) :=
    (hout _ (by omega)).trans (counted.counts _ (by omega))
  have hread : μ' (s + j) = L[j] := (hout _ (by omega)).trans (hL j hj)
  -- The value that is written fits in a word.
  have hV : |sg * L[j]| ≤ (a.V : ℤ) := by
    rcases H.sign with rfl | rfl <;> simpa using H.bucket.bounded.getElem hj
  have := abs_le.1 hV
  have := abs_mul sg L[j]
  have := abs_le.1 (le_refl |g|)
  -- key := mem[fr + j]
  light_set K[j] using hkey
  -- if mem[cnt + key] = 1
  light_if hone hmany : K.count K[j] = 1 using hcount
  · -- ad := y + 4 * key + off; w := sg * mem[s + j] + g
    light_set (a.y + 4 * K[j] + off : ℕ)
    light_set (sg * L[j] + g) using hread
    -- mem[ad] := w; mem[ad + δ] := w
    light_store (a.y + 4 * K[j] + off) (sg * L[j] + g)
    light_store (a.y + 4 * K[j] + off + δ) (sg * L[j] + g)
    refine ⟨⟨j, (a.y + 4 * K[j] + off : ℕ), K[j], sg * L[j] + g, x.res, x.fr2⟩, _, rfl, ?_⟩
    rw [hval j hjK hj hone]
    exact inv.succ_one hjK hkey_lt hone H.dist
  · light_skip
    exact ⟨{ x with key := K[j] }, μ', rfl, inv.succ_many hjK hmany⟩

/-- **The loop of a pass.**  μ₀ is the memory at the start of the pass, μ the memory at the start of
the loop. -/
theorem placeLoop_ends (H : PassPre lim μ₀ d a sg g s off δ cap ylen L) (hlen : K.length = L.length)
    (hlt : ∀ q ∈ K, q < a.Mo) (counted : Counted μ a.fr a.cnt cap K) (hL : Seg μ s L)
    (hval : ∀ j (hK : j < K.length) (hj : j < L.length), K.count K[j] = 1 →
      sg * L[j] + g = val K[j]) (x : ArrScratch) :
    Ends lim P d placeLoop ⟨frame (arrLocals a x sg g s L.length off δ), μ⟩ (45 * L.length + 6)
      fun σ' => ∃ (x' : ArrScratch) (μ' : ℕ → ℤ),
        σ' = ⟨frame (arrLocals a x' sg g s L.length off δ), μ'⟩ ∧
        PlaceInv μ μ' a.y off δ a.Mo K val L.length := by
  have := sq_add_le_word H.bucket.ok.word
  have : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  -- for j < len; the scratch variables hold anything
  exact Ends.forShape
    (fun j x' μ' => ⟨frame (arrLocals a { x' with idx := j } sg g s L.length off δ), μ'⟩)
    (fun j μ' => PlaceInv μ μ' a.y off δ a.Mo K val j) L.length 37 x .zero
    (fun j x' μ' hj inv => placeRound_ends H hlen hlt counted hL hval x' hj inv)
    (fun x' μ' inv => ⟨_, μ', rfl, inv⟩)

/-- **One pass.**  val r is what the cells of the remainder r are to hold if r has the count 1. -/
theorem place_ends {pResid pTally : ℕ} (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (H : PassPre lim μ d a sg g s off δ cap ylen L)
    (hval : ∀ j (hj : j < L.length),
      (keys a.Mo (L.map (sg * ·))).count ((sg * L[j]) % (a.Mo : ℤ)).toNat = 1 →
        sg * L[j] + g = val ((sg * L[j]) % (a.Mo : ℤ)).toNat) (x : ArrScratch) :
    Ends lim P d (placeStmt pResid pTally) ⟨frame (arrLocals a x sg g s L.length off δ), μ⟩
      (tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : ℕ → ℤ), σ' = ⟨frame (arrLocals a x' sg g s L.length off δ), μ'⟩ ∧
        (∀ r < a.Mo, ∀ e, (e = 0 ∨ e = δ) → μ' (a.y + 4 * r + off + e) =
          if (keys a.Mo (L.map (sg * ·))).count r = 1 then val r
          else μ (a.y + 4 * r + off + e)) ∧
        SameOn (fun b => b < a.fr ∧ ¬ PlaceCell a.y off δ a.Mo b) μ μ' := by
  have C := H.bucket
  simp only [tPlace]
  have hlen : (keys a.Mo (L.map (sg * ·))).length = L.length := by simp
  have hlt := keys_lt C.modulus_pos (L.map (sg * ·))
  have := sq_add_le_word C.ok.word
  have : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  light_facts H C C.ok
  have hcells := C.ok.cells
  have hdepth := C.ok.depth
  simp only [collNeed] at hcells hdepth
  -- fr' := fr + len
  light_set (a.fr + L.length : ℕ)
  -- resid(len, s, sg, M, fr, fr')
  light_call (C.resid_meets hR H.sign) with - μ₁ ⟨hkeys, kept₁⟩
  -- tally(len, fr, cnt, 1)
  light_call (C.count_meets hT hlen hlt hkeys kept₁) with res μ₂ ⟨counted, kept₂⟩
  -- the loop
  light_piece (placeLoop_ends H hlen hlt counted (C.list.of_sameOn kept₂ fun i hi => by omega)
    (fun j _ hj hone => by simpa [keys] using hval j hj (by simpa [keys] using hone))
    { x with res := res, fr2 := (a.fr + L.length : ℕ) }) with _ ⟨x₃, μ₃, rfl, inv⟩
  have same₃ : SameOutside μ₂ μ₃ a.y ylen := SameOn.mono inv.rest fun b hb hcell => by
    have := H.placeCell_lt hcell
    omega
  -- tally(len, fr, cnt, -1)
  light_call (C.uncount_meets hT hlen hlt (counted.of_sameOutside same₃ H.belowArr H.apartTable))
    with res' μ₄ ⟨zero₄, same₄⟩
  refine ⟨{ x₃ with res := res' }, μ₄, rfl, fun r hr e he => ?_, ?_⟩
  · have hcell := H.placeCell_lt (b := a.y + 4 * r + off + e) ⟨r, hr, by omega⟩
    rw [← hlen] at inv
    rw [same₄ _ (by omega), inv.done hr he, kept₂ _ (by omega)]
  · exact sameOn_of_zeroAt ((kept₂.then inv.rest fun b hb => ⟨⟨hb.1.1, hb.2⟩, hb.1.2⟩).then same₄
      fun b hb => ⟨hb, hb.2⟩) C.zero zero₄

/-- One pass, in terms of the array `arr` of the set of the numbers sg · x: if the cells hold pd + g
before, for a padding value pd, they hold the entries of the array, plus g, afterwards. -/
theorem place_arr {pResid pTally : ℕ} (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (H : PassPre lim μ d a sg g s off δ cap ylen L) (hnd : L.Nodup) {pd : ℤ}
    (hpad : ∀ r < a.Mo, ∀ e, (e = 0 ∨ e = δ) → μ (a.y + 4 * r + off + e) = pd + g)
    (x : ArrScratch) :
    Ends lim P d (placeStmt pResid pTally) ⟨frame (arrLocals a x sg g s L.length off δ), μ⟩
      (tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : ℕ → ℤ), σ' = ⟨frame (arrLocals a x' sg g s L.length off δ), μ'⟩ ∧
        (∀ r < a.Mo, ∀ e, (e = 0 ∨ e = δ) → μ' (a.y + 4 * r + off + e) =
          arr (L.map (sg * ·)).toFinset a.Mo pd r + g) ∧
        SameOn (fun b => b < a.fr ∧ ¬ PlaceCell a.y off δ a.Mo b) μ μ' := by
  have hM := H.bucket.modulus_pos
  have : (L.map (sg * ·)).Nodup := hnd.map fun u w huw => by
    rcases H.sign with rfl | rfl <;> simpa using huw
  refine (place_ends hR hT H (val := fun r => arr (L.map (sg * ·)).toFinset a.Mo pd r + g)
    (fun j hj hone => ?_) x).mono le_rfl ?_
  · have h := arr_of_count_eq_one hM this pd (j := j) (by simpa using hj)
    simp only [List.getElem_map] at h
    rw [h hone]
  · rintro _ ⟨x', μ', rfl, hcells, hrest⟩
    refine ⟨x', μ', rfl, fun r hr e he => ?_, hrest⟩
    rw [hcells r hr e he]
    split_ifs with hone
    · rfl
    · rw [arr_of_count_ne_one hM this pd hone, hpad r hr e he]

end pass

/-! ## A pass, in terms of the cells number off of the groups -/

/-- No cell below the free pointer has changed, except cell t of the c groups from y. -/
abbrev KeptCol (μ μ' : ℕ → ℤ) (fr y c t : ℕ) : Prop :=
  SameOn (fun b => b < fr ∧ ∀ i < c, b ≠ y + 4 * i + t) μ μ'

/-- A cell of another kind has not changed. -/
theorem KeptCol.cell {μ μ' : ℕ → ℤ} {fr y c t : ℕ} (h : KeptCol μ μ' fr y c t) {i t' : ℕ}
    (hb : y + 4 * i + t' < fr) (ht : t < 4 := by omega) (ht' : t' < 4 := by omega)
    (hne : t' ≠ t := by omega) : μ' (y + 4 * i + t') = μ (y + 4 * i + t') :=
  h _ ⟨hb, fun _ _ => by omega⟩

/-- The cells outside the array have not changed either. -/
theorem KeptCol.keptBut {μ μ' μ'' : ℕ → ℤ} {fr y c t : ℕ} (h : KeptCol μ' μ'' fr y c t)
    (hk : KeptBut μ μ' fr y (4 * c)) (ht : t < 4 := by omega) : KeptBut μ μ'' fr y (4 * c) :=
  hk.then h fun b hb => ⟨hb, hb.1, fun i hi => by have := hb.2; omega⟩

section column

variable {μ : ℕ → ℤ} {a : ArrArgs} {g pd : ℤ} {s off cap c : ℕ} {L : List ℤ} {pResid pTally : ℕ}

/-- **A pass for the first or the second set**: if cell off of each of the c groups holds pd + g
before, then afterwards cell off of group i holds entry i of the array of the set with the padding
value pd, plus g, and no other cell below the free pointer has changed. -/
theorem place_col (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (H : PassPre lim μ d a 1 g s off 0 cap (4 * c) L) (hnd : L.Nodup)
    (hpad : ∀ i < c, μ (a.y + 4 * i + off) = pd + g) (x : ArrScratch) :
    Ends lim P d (placeStmt pResid pTally) ⟨frame (arrLocals a x 1 g s L.length off 0), μ⟩
      (tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : ℕ → ℤ), σ' = ⟨frame (arrLocals a x' 1 g s L.length off 0), μ'⟩ ∧
        (∀ i < c, μ' (a.y + 4 * i + off) = arr L.toFinset a.Mo pd i + g) ∧
        KeptCol μ μ' a.fr a.y c off := by
  light_facts H
  refine (place_arr hR hT H hnd (pd := pd) (fun r hr e he => ?_) x).mono le_rfl ?_
  · obtain rfl : e = 0 := by omega
    exact hpad r (by omega)
  rintro _ ⟨x', μ', rfl, hcells, hrest⟩
  refine ⟨x', μ', rfl, fun i hi => ?_, SameOn.mono hrest fun b hb => ⟨hb.1, ?_⟩⟩
  · by_cases hiM : i < a.Mo
    · simpa using hcells i hiM 0 (Or.inl rfl)
    · rw [hrest _ ⟨by omega, fun ⟨r, hr, hEq⟩ => by omega⟩,
        arr_of_le H.bucket.modulus_pos _ _ (by omega), hpad i hi]
  · rintro ⟨r, hr, hEq⟩
    exact hb.2 r (by omega) (by omega)

/-- **The pass for the third set**: if cell off of each of the c groups holds -(2V + 1) + g before,
then afterwards cell off of group i holds entry i of the third array of the node, plus g, and no
other cell below the free pointer has changed. -/
theorem place_colZ (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (H : PassPre lim μ d a (-1) g s off (4 * a.Mo) cap (4 * c) L) (hnd : L.Nodup)
    (hpad : ∀ i < c, μ (a.y + 4 * i + off) = -(2 * a.V + 1) + g) (x : ArrScratch) :
    Ends lim P d (placeStmt pResid pTally)
      ⟨frame (arrLocals a x (-1) g s L.length off (4 * a.Mo)), μ⟩
      (tPlace L.length a.V) fun σ' =>
      (∀ i < c, σ'.mem (a.y + 4 * i + off) = arrZ L.toFinset a.Mo a.V i + g) ∧
        KeptCol μ σ'.mem a.fr a.y c off := by
  light_facts H
  have himage : (L.map (-1 * ·)).toFinset = L.toFinset.image fun u => -u := by
    ext u
    simp
  refine (place_arr hR hT H hnd (pd := -(2 * a.V + 1)) (fun r hr e he => ?_) x).mono le_rfl ?_
  · rcases he with rfl | rfl
    · exact hpad r (by omega)
    · rw [show a.y + 4 * r + off + 4 * a.Mo = a.y + 4 * (r + a.Mo) + off by ring]
      exact hpad _ (by omega)
  rintro _ ⟨x', μ', rfl, hcells, hrest⟩
  rw [himage] at hcells
  refine ⟨fun i hi => ?_, SameOn.mono hrest fun b hb => ⟨hb.1, ?_⟩⟩
  · change μ' (a.y + 4 * i + off) = _
    unfold arrZ pad
    by_cases hiM : i < a.Mo
    · rw [if_pos (by omega), Nat.mod_eq_of_lt hiM]
      simpa using hcells i hiM 0 (Or.inl rfl)
    · by_cases hi2 : i < 2 * a.Mo
      · have h := hcells (i - a.Mo) (by omega) (4 * a.Mo) (Or.inr rfl)
        rw [show a.y + 4 * (i - a.Mo) + off + 4 * a.Mo = a.y + 4 * i + off by omega] at h
        rw [if_pos hi2, Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
        simpa using h
      · rw [if_neg hi2, hrest _ ⟨by omega, fun ⟨r, hr, hEq⟩ => by omega⟩, hpad i hi]
  · rintro ⟨r, hr, hEq | hEq⟩
    · exact hb.2 r (by omega) hEq
    · exact hb.2 (r + a.Mo) (by omega) (by omega)

end column

/-! ## The routine -/

open ArrLocals in
/-- The constants: W = 2V + 1, G = 3W + 1, the number 2m² of groups, and the padding pattern. -/
def arrConsts : Stmt :=
  .set WIDTH (k 2 *' v VMAX +' k 1) ;;
  .set GAP (k 3 *' v WIDTH +' k 1) ;;
  .set GROUPS (k 2 *' (v MMAX *' v MMAX)) ;;
  .set PAD0 (k 10 *' v GAP) ;;
  .set PAD1 (v WIDTH +' v GAP) ;;
  .set PAD2 (v WIDTH +' k 3 *' v GAP) ;;
  .set PAD3 (k 4 *' v GAP -' v WIDTH)

open ArrLocals in
/-- The pass for the first set: x + G goes to cell 1 of the group of its remainder. -/
def arrPass₁ (pResid pTally : ℕ) : Stmt :=
  .set SIGN (k 1) ;;
  .set SHIFT (v GAP) ;;
  .set SRC (v SET1) ;;
  .set LEN (v LEN1) ;;
  .set OFF (k 1) ;;
  .set DIST (k 0) ;;
  placeStmt pResid pTally

open ArrLocals in
/-- The pass for the second set: x + 3G goes to cell 2 of the group of its remainder.  The sign 1
and the distance 0 are as the first pass left them. -/
def arrPass₂ (pResid pTally : ℕ) : Stmt :=
  .set SHIFT (k 3 *' v GAP) ;; .set SRC (v SET2) ;; .set LEN (v LEN2) ;; .set OFF (k 2) ;;
  placeStmt pResid pTally

open ArrLocals in
/-- The pass for the third set: -x + 4G goes to cell 3 of the groups r and r + M, where r is the
remainder of -x. -/
def arrPass₃ (pResid pTally : ℕ) : Stmt :=
  .set SIGN (k 0 -' k 1) ;; .set SHIFT (k 4 *' v GAP) ;; .set SRC (v SET3) ;; .set LEN (v LEN3) ;;
  .set OFF (k 3) ;; .set DIST (k 4 *' v MOD) ;;
  placeStmt pResid pTally

/-- nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr), over the procedures number pResid and
pTally. -/
def nodeArrayBody (pResid pTally : ℕ) : Stmt :=
  arrConsts ;; padStmt ;; arrPass₁ pResid pTally ;; arrPass₂ pResid pTally ;;
  arrPass₃ pResid pTally

/-- What nodeArray assumes, apart from the three sets: the modulus, the count table, the place of
the array, and the limits. -/
structure ArrPre (lim : Limits) (μ : ℕ → ℤ) (d n : ℕ) (a : ArrArgs) : Prop where
  modulus_pos : 1 ≤ a.Mo
  modulus_le : a.Mo ≤ a.m * a.m
  zero : ZeroAt μ a.cnt (a.m * a.m)
  belowTable : a.cnt + a.m * a.m ≤ a.fr
  belowArr : a.y + 4 * (2 * (a.m * a.m)) ≤ a.fr
  apartTable : Apart a.y (4 * (2 * (a.m * a.m))) a.cnt (a.m * a.m)
  ok : (nodeArrayNeed n a.V a.m).Ok lim a.fr d

/-- What nodeArray assumes about one of the three sets, given as the list L at s. -/
structure ArrSet (μ : ℕ → ℤ) (n : ℕ) (a : ArrArgs) (s : ℕ) (L : List ℤ) : Prop where
  list : Seg μ s L
  nodup : L.Nodup
  bounded : AbsLe L a.V
  le : L.length ≤ n
  below : s + L.length ≤ a.fr
  apartTable : Apart s L.length a.cnt (a.m * a.m)
  apartArr : Apart a.y (4 * (2 * (a.m * a.m))) s L.length

section routine

variable {μ μ' : ℕ → ℤ} {n : ℕ} {a : ArrArgs} {s : ℕ} {L : List ℤ} {pResid pTally : ℕ}

/-- The assumptions do not depend on the cells of the array. -/
theorem ArrPre.keptBut (h : ArrPre lim μ d n a)
    (hk : KeptBut μ μ' a.fr a.y (4 * (2 * (a.m * a.m)))) : ArrPre lim μ' d n a := by
  light_facts h
  exact { h with zero := fun q hq => (hk _ (by omega)).trans (h.zero q hq) }

/-- The assumptions about a set do not depend on the cells of the array. -/
theorem ArrSet.keptBut (h : ArrSet μ n a s L)
    (hk : KeptBut μ μ' a.fr a.y (4 * (2 * (a.m * a.m)))) : ArrSet μ' n a s L := by
  light_facts h
  exact { h with list := h.list.of_sameOn hk fun i hi => by omega }

/-- The numbers up to 64 (V + 1) fit in a word. -/
theorem ArrPre.word_le (h : ArrPre lim μ d n a) : 64 * ((a.V : ℤ) + 1) ≤ lim.word := by
  simpa using mul_le_word (x := 1) (y := 1) (z := 64 * (a.V + 1)) h.ok.word
    (Nat.one_le_pow _ _ (by omega)) (by omega) le_rfl

/-- What a pass assumes, from what nodeArray assumes. -/
theorem ArrPre.pass (h : ArrPre lim μ d n a) (hS : ArrSet μ n a s L) {sg g : ℤ} {off δ : ℕ}
    (hsg : sg = 1 ∨ sg = -1) (hoff : off < 4) (hδ : δ = 0 ∨ δ = 4 * a.Mo)
    (hg₀ : 0 ≤ g) (hg : g ≤ 32 * ((a.V : ℤ) + 1)) :
    PassPre lim μ d a sg g s off δ (a.m * a.m) (4 * (2 * (a.m * a.m))) L := by
  have hM := h.modulus_le
  have := h.word_le
  have hle := hS.le
  have := abs_of_nonneg hg₀
  exact
    { bucket :=
        { modulus_pos := h.modulus_pos
          modulus_le := hM
          bounded := hS.bounded
          list := hS.list
          zero := h.zero
          belowList := hS.below
          belowTable := h.belowTable
          apart := hS.apartTable
          ok := h.ok.mono (wordNeed_mono hle hM) (by simp only [collNeed, nodeArrayNeed]; omega)
            le_rfl }
      sign := hsg
      belowArr := h.belowArr
      apartSet := hS.apartArr
      apartTable := h.apartTable
      room := by omega
      off_lt := hoff
      dist := by omega
      value_le := by omega }

/-- **The constants** are computed. -/
theorem arrConsts_ends (h : ArrPre lim μ d n a) :
    Ends lim P d arrConsts
      ⟨frame [a.Mo, a.s₁, a.l₁, a.s₂, a.l₂, a.s₃, a.l₃, a.V, a.m, a.y, a.cnt, a.fr], μ⟩ 38
      fun σ' => σ' = ⟨frame (arrLocals a ⟨0, 0, 0, 0, 0, 0⟩ 0 0 0 0 0 0), μ⟩ := by
  have hword := h.word_le
  light_facts h h.ok
  have hnonneg : (0 : ℤ) ≤ (a.m : ℤ) * a.m := by positivity
  have habs : |6 * (a.V : ℤ) + 4| = 6 * a.V + 4 := abs_of_nonneg (by positivity)
  have hgroups : 8 * ((a.m : ℤ) * a.m) ≤ lim.space := by
    have : 8 * (a.m * a.m) ≤ lim.space := by omega
    exact_mod_cast this
  -- W := 2 V + 1; G := 3 W + 1; groups := 2 (m m)
  light_set (2 * a.V + 1)
  light_set (6 * a.V + 4)
  light_set (2 * (a.m * a.m) : ℕ)
  -- the padding pattern 10 G, W + G, W + 3 G, 4 G - W
  light_set (padVal a.V 0) using padVal
  light_set (padVal a.V 1) using padVal
  light_set (padVal a.V 2) using padVal
  light_set (padVal a.V 3) using padVal
  rfl

/-- **The pass for the first set.** -/
theorem arrPass₁_ends (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (h : ArrPre lim μ d n a) (hS : ArrSet μ n a a.s₁ L) (hl : a.l₁ = L.length)
    (hpad : ∀ i < 2 * (a.m * a.m), μ (a.y + 4 * i + 1) = padVal a.V 1) {x : ArrScratch}
    {sg g : ℤ} {s len off δ : ℕ} :
    Ends lim P d (arrPass₁ pResid pTally) ⟨frame (arrLocals a x sg g s len off δ), μ⟩
      (12 + tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : ℕ → ℤ),
        σ' = ⟨frame (arrLocals a x' 1 (6 * a.V + 4) a.s₁ L.length 1 0), μ'⟩ ∧
        (∀ i < 2 * (a.m * a.m), μ' (a.y + 4 * i + 1) =
          arr L.toFinset a.Mo (2 * a.V + 1) i + (6 * a.V + 4)) ∧
        KeptCol μ μ' a.fr a.y (2 * (a.m * a.m)) 1 := by
  have := h.word_le
  -- sg := 1; g := G; s := s₁; len := l₁; off := 1; δ := 0
  light_set 1
  light_set (6 * a.V + 4)
  light_set a.s₁
  light_set L.length using hl
  light_set (1 : ℕ)
  light_set (0 : ℕ)
  light_piece (place_col hR hT (h.pass hS (Or.inl rfl) (by omega) (Or.inl rfl)
    (by positivity) (by omega)) hS.nodup (pd := 2 * a.V + 1)
    (fun i hi => by rw [hpad i hi]; simp [padVal]) x)

/-- **The pass for the second set.** -/
theorem arrPass₂_ends (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (h : ArrPre lim μ d n a) (hS : ArrSet μ n a a.s₂ L) (hl : a.l₂ = L.length)
    (hpad : ∀ i < 2 * (a.m * a.m), μ (a.y + 4 * i + 2) = padVal a.V 2) {x : ArrScratch}
    {g : ℤ} {s len off : ℕ} :
    Ends lim P d (arrPass₂ pResid pTally) ⟨frame (arrLocals a x 1 g s len off 0), μ⟩
      (10 + tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : ℕ → ℤ),
        σ' = ⟨frame (arrLocals a x' 1 (3 * (6 * a.V + 4)) a.s₂ L.length 2 0), μ'⟩ ∧
        (∀ i < 2 * (a.m * a.m), μ' (a.y + 4 * i + 2) =
          arr L.toFinset a.Mo (2 * a.V + 1) i + 3 * (6 * a.V + 4)) ∧
        KeptCol μ μ' a.fr a.y (2 * (a.m * a.m)) 2 := by
  have := h.word_le
  have : |6 * (a.V : ℤ) + 4| = 6 * a.V + 4 := abs_of_nonneg (by positivity)
  -- g := 3 G; s := s₂; len := l₂; off := 2
  light_set (3 * (6 * a.V + 4))
  light_set a.s₂
  light_set L.length using hl
  light_set (2 : ℕ)
  light_piece (place_col hR hT (h.pass hS (Or.inl rfl) (by omega) (Or.inl rfl)
    (by positivity) (by omega)) hS.nodup (pd := 2 * a.V + 1)
    (fun i hi => by rw [hpad i hi]; simp [padVal]) x)

/-- **The pass for the third set.** -/
theorem arrPass₃_ends (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (h : ArrPre lim μ d n a) (hS : ArrSet μ n a a.s₃ L) (hl : a.l₃ = L.length)
    (hpad : ∀ i < 2 * (a.m * a.m), μ (a.y + 4 * i + 3) = padVal a.V 3) {x : ArrScratch}
    {sg g : ℤ} {s len off δ : ℕ} :
    Ends lim P d (arrPass₃ pResid pTally) ⟨frame (arrLocals a x sg g s len off δ), μ⟩
      (18 + tPlace L.length a.V) fun σ' =>
      (∀ i < 2 * (a.m * a.m), σ'.mem (a.y + 4 * i + 3) =
        arrZ L.toFinset a.Mo a.V i + 4 * (6 * a.V + 4)) ∧
      KeptCol μ σ'.mem a.fr a.y (2 * (a.m * a.m)) 3 := by
  have := h.word_le
  have : |6 * (a.V : ℤ) + 4| = 6 * a.V + 4 := abs_of_nonneg (by positivity)
  light_facts h h.ok
  -- sg := -1; g := 4 G; s := s₃; len := l₃; off := 3; δ := 4 M
  light_set (-1)
  light_set (4 * (6 * a.V + 4))
  light_set a.s₃
  light_set L.length using hl
  light_set (3 : ℕ)
  light_set (4 * a.Mo : ℕ)
  light_piece (place_colZ hR hT (h.pass hS (Or.inr rfl) (by omega) (Or.inr rfl)
    (by positivity) (by omega)) hS.nodup (fun i hi => by rw [hpad i hi]; simp [padVal]) x)

/-- The four kinds of cells make up the one-array instance of the node. -/
theorem oneArray_of_cells {ν : Node} {V y c : ℕ} (h₀ : ∀ i < c, μ (y + 4 * i + 0) = padVal V 0)
    (h₁ : ∀ i < c, μ (y + 4 * i + 1) = arr ν.S₁ ν.M (2 * V + 1) i + (6 * V + 4))
    (h₂ : ∀ i < c, μ (y + 4 * i + 2) = arr ν.S₂ ν.M (2 * V + 1) i + 3 * (6 * V + 4))
    (h₃ : ∀ i < c, μ (y + 4 * i + 3) = arrZ ν.S₃ ν.M V i + 4 * (6 * V + 4)) :
    ∀ u < 4 * c, μ (y + u) = ν.oneArray V u := by
  intro u hu
  obtain ⟨i, t, ht, rfl⟩ : ∃ i t, t < 4 ∧ u = 4 * i + t :=
    ⟨u / 4, u % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod u 4).symm⟩
  obtain ⟨c₀, c₁, c₂, c₃⟩ := oneArray_cells ν V i
  rw [← Nat.add_assoc]
  interval_cases t
  · rw [h₀ i (by omega), Nat.add_zero, c₀]
    simp [padVal]
  · rw [h₁ i (by omega), c₁]
  · rw [h₂ i (by omega), c₂]
  · rw [h₃ i (by omega), c₃]

/-- **The whole routine**, for the arguments a and the three sets as lists. -/
theorem nodeArrayBody_ends {L₁ L₂ L₃ : List ℤ} (hR : ResidSpec lim P pResid)
    (hT : TallySpec lim P pTally) (h : ArrPre lim μ d n a) (hS₁ : ArrSet μ n a a.s₁ L₁)
    (hS₂ : ArrSet μ n a a.s₂ L₂) (hS₃ : ArrSet μ n a a.s₃ L₃) (hl₁ : a.l₁ = L₁.length)
    (hl₂ : a.l₂ = L₂.length) (hl₃ : a.l₃ = L₃.length) :
    Ends lim P d (nodeArrayBody pResid pTally)
      ⟨frame [a.Mo, a.s₁, a.l₁, a.s₂, a.l₂, a.s₃, a.l₃, a.V, a.m, a.y, a.cnt, a.fr], μ⟩
      (42 * (2 * (a.m * a.m)) + tPlace L₁.length a.V + tPlace L₂.length a.V + tPlace L₃.length a.V
        + 84) fun σ' =>
      (∀ u < 4 * (2 * (a.m * a.m)), σ'.mem (a.y + u) =
        Node.oneArray ⟨L₁.toFinset, L₂.toFinset, L₃.toFinset, a.Mo⟩ a.V u) ∧
      KeptBut μ σ'.mem a.fr a.y (4 * (2 * (a.m * a.m))) := by
  light_facts h h.ok
  -- the constants
  light_piece (arrConsts_ends h) with _ rfl
  -- the padding pattern
  light_piece (pad_ends h.ok.space (by omega)) with _ ⟨μ₀, ⟨hpad, same₀⟩, rfl⟩
  have kept₀ : KeptBut μ μ₀ a.fr a.y (4 * (2 * (a.m * a.m))) := SameOn.mono same₀ fun _ hb => hb.2
  -- the first set
  light_piece (arrPass₁_ends hR hT (h.keptBut kept₀) (hS₁.keptBut kept₀) hl₁
    fun i hi => hpad i hi 1 (by omega)) with _ ⟨x₁, μ₁, rfl, col₁, same₁⟩
  have kept₁ := same₁.keptBut kept₀
  -- the second set
  light_piece (arrPass₂_ends hR hT (h.keptBut kept₁) (hS₂.keptBut kept₁) hl₂
    fun i hi => (same₁.cell (by omega)).trans (hpad i hi 2 (by omega)))
    with _ ⟨x₂, μ₂, rfl, col₂, same₂⟩
  have kept₂ := same₂.keptBut kept₁
  -- the third set
  light_piece (arrPass₃_ends hR hT (h.keptBut kept₂) (hS₃.keptBut kept₂) hl₃
    fun i hi => (same₂.cell (by omega)).trans ((same₁.cell (by omega)).trans
      (hpad i hi 3 (by omega)))) with ⟨_, μ₃⟩ ⟨col₃, same₃⟩
  -- Each pass has left the cells of the other kinds as they were.
  refine ⟨oneArray_of_cells (fun i hi => ?_) (fun i hi => ?_) (fun i hi => ?_) col₃,
    same₃.keptBut kept₂⟩
  · exact (same₃.cell (by omega)).trans
      ((same₂.cell (by omega)).trans
        ((same₁.cell (by omega)).trans (hpad i hi 0 (by omega))))
  · exact (same₃.cell (by omega)).trans
      ((same₂.cell (by omega)).trans (col₁ i hi))
  · exact (same₃.cell (by omega)).trans (col₂ i hi)

end routine

/-- **nodeArray meets its specification**, in every program that holds its body and meets the
specifications of the two routines that it calls. -/
theorem nodeArray_spec {p pResid pTally : ℕ} (hp : P[p]? = some (nodeArrayBody pResid pTally))
    (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally) : NodeArraySpec lim P p := by
  rintro ⟨⟨fr, n, V, m, np, pr, cnt⟩, ⟨s₁, l₁, S₁⟩, ⟨s₂, l₂, S₂⟩, ⟨s₃, l₃, S₃⟩⟩ Mo y μ
    ⟨henv, h₁, h₂, h₃⟩ hM hMm ⟨hy, ay₁, ay₂, ay₃, ayc⟩ d hok
  obtain ⟨L₁, rfl, seg₁, nodup₁, rfl⟩ : SetAt μ s₁ l₁ S₁ := h₁.set
  obtain ⟨L₂, rfl, seg₂, nodup₂, rfl⟩ : SetAt μ s₂ l₂ S₂ := h₂.set
  obtain ⟨L₃, rfl, seg₃, nodup₃, rfl⟩ : SetAt μ s₃ l₃ S₃ := h₃.set
  have hsq : 8 * m ^ 2 = 4 * (2 * (m * m)) := by ring
  dsimp only at hy ay₁ ay₂ ay₃ ayc hM hMm hok ⊢
  rw [hsq] at hy ay₁ ay₂ ay₃ ayc ⊢
  refine .of_body hp ((nodeArrayBody_ends (n := n)
    (a := ⟨Mo, s₁, L₁.length, s₂, L₂.length, s₃, L₃.length, V, m, y, cnt, fr⟩) hR hT
    ⟨hM, hMm, henv.zero, henv.belowCnt, hy, ayc, hok⟩
    ⟨seg₁, nodup₁, fun x hx => h₁.bdd x (List.mem_toFinset.2 hx), h₁.le, h₁.below, h₁.apart, ay₁⟩
    ⟨seg₂, nodup₂, fun x hx => h₂.bdd x (List.mem_toFinset.2 hx), h₂.le, h₂.below, h₂.apart, ay₂⟩
    ⟨seg₃, nodup₃, fun x hx => h₃.bdd x (List.mem_toFinset.2 hx), h₃.le, h₃.below, h₃.apart, ay₃⟩
    rfl rfl rfl).mono ?_ fun _ h => h)
  simp only [tNodeArray, tPlace, sq]
  omega

end Light.Sec3.ChanHe
end
