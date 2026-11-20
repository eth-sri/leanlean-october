/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module
public import ImprovedExponents.PrunedProgram.Boxes.All

/-! Enumerate low leaves and the disjoint boxes for the output string. A box is
read by its radix-11 code in the precomputed page of the tile. -/
@[expose] public section
namespace Light.Sec4.BoxTable
open ThreeSumApsp ThreeSumApsp.Spec

structure QueryCoreArgs extends Tile where
  (wd ss : ℕ)
  η : OutStr L

def QueryCoreArgs.terms (x : QueryCoreArgs) :=
  queryTerms x.m x.t (arrT x.A) (arrT x.B) x.toTile.val (digitsO x.η)

structure Pre (lim : Limits) (μ : ℕ → ℤ) (x : QueryCoreArgs) : Prop where
  std : Std lim
  t_le : x.t ≤ x.m
  card : (innerSetO x.η).card = x.m
  segA : SegOn x.m μ x.a x.A
  segB : SegOn x.m μ x.b x.B
  read : ∀ l ∈ boxesOf x.m x.t (digitsO x.η), μ (x.page+ofDigitList 11 l) = x.toTile.val l
  segDigits : SegN μ x.wd (digitsO x.η)
  sums : ∀ j, |(x.terms.take j).sum| ≤ lim.word
  prod : ∀ τ, |x.A τ * x.B τ| ≤ lim.word
  pow : 10^x.L ≤ lim.word
  layout : x.a+10^x.L ≤ x.wd ∧ x.b+10^x.L ≤ x.wd ∧ x.wd+x.L ≤ x.box ∧ x.box+x.L ≤ x.ss ∧
    x.ss+x.m ≤ x.page ∧ x.page+stride x.L < lim.space

def QueryCoreSpecP (lim : Limits) (P : Program) := ∀ x μ, Pre lim μ x → ∀ d, d+1 ≤ lim.depth →
  Meets lim P Proc.queryCore d [x.a,x.b,x.page,x.wd,x.ss,x.box,x.L,x.m,x.t] μ (tQueryCore x.L x.m x.t)
    fun r ν => r = x.terms.sum ∧ SameOutside2 μ ν x.ss x.m x.box x.L

namespace Query

slots 0 EncA EncB Page Digits Str Box Levels Inner Switch Sum More Code Value Nines

end Query

open Query in
def queryLowRound : Stmt :=
  .call Proc.scatter [v Digits, v Str, v Box, v Levels, k 0] Code ;;
  .call Proc.horner [v Box, v Levels] Code ;;
  .set Sum (v Sum +' M (v EncA +' v Code) *' M (v EncB +' v Code)) ;;
  .call Proc.nineNext [v Str, v Inner, v Nines +' k 1, v Inner] More

open Query in
def queryBoxRound : Stmt :=
  .call Proc.scatter [v Digits, v Str, v Box, v Levels, k 1] Code ;;
  .call Proc.lookup [v Box, v Levels] Value ;;
  .set Sum (v Sum +' M (v Page +' v Value)) ;;
  .call Proc.nineNext [v Str, v Inner, v Nines, v Nines] More

open Query in
def queryLow : Stmt :=
  .call Proc.nineFirst [v Str, v Inner, v Nines +' k 1] More ;;
  .set More (k 1) ;;
  .while (v More =' k 1) queryLowRound

open Query in
def queryBoxes : Stmt :=
  .call Proc.nineFirst [v Str, v Inner, v Nines] More ;;
  .set More (k 1) ;;
  .while (v More =' k 1) queryBoxRound

open Query in
def queryCoreBody : Stmt :=
  .set Nines (v Inner -' v Switch) ;;
  .ite (v Switch =' k 0) .skip queryLow ;;
  queryBoxes ;;
  .set EncA (v Sum)

namespace Query

variable {μ : ℕ → ℤ} {x : QueryCoreArgs} {i : ℕ} {σ : State}

abbrev lowCount (x : QueryCoreArgs) : ℕ := (nineStrs x.m (x.m - x.t + 1) x.m).length

abbrev boxCount (x : QueryCoreArgs) : ℕ := (nineStrs x.m (x.m - x.t) (x.m - x.t)).length

theorem length_digits (x : QueryCoreArgs) : (digitsO x.η).length = x.L := length_digitsO x.η

def leafAt (x : QueryCoreArgs) (i : ℕ) : List ℕ :=
  scatter (digitsO x.η) (nineStr x.m (x.m - x.t + 1) x.m i)

def boxAt (x : QueryCoreArgs) (i : ℕ) : List ℕ :=
  scatter (digitsO x.η) (starRunIf true (nineStr x.m (x.m - x.t) (x.m - x.t) i))

theorem box_term (hi : i < boxCount x) :
    boxAt x i ∈ boxesOf x.m x.t (digitsO x.η) ∧
      (x.terms.take (lowCount x + (i + 1))).sum = (x.terms.take (lowCount x + i)).sum +
        x.toTile.val (boxAt x i) := by
  refine ⟨List.mem_map.mpr ⟨_, nineStr_mem hi, rfl⟩, ?_⟩
  have hlows : ((lowList x.m x.t (digitsO x.η)).map
      (leafProduct (arrT x.A) (arrT x.B))).length = lowCount x := by simp [lowList]
  have hlen : i < (boxesOf x.m x.t (digitsO x.η)).length := by simpa [boxesOf] using hi
  have hmember : (boxesOf x.m x.t (digitsO x.η))[i] = boxAt x i := by
    refine Option.some.inj ((List.getElem?_eq_getElem hlen).symm.trans ?_)
    rw [boxesOf, List.getElem?_map, List.getElem?_eq_getElem hi, getElem_nineStrs hi]
    rfl
  rw [← Nat.add_assoc, List.sum_take_succ_getD, QueryCoreArgs.terms, queryTerms, ← hlows,
    List.getD_append_add,
    List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getElem_map, hmember]

theorem same_of_box {ν ν' : ℕ → ℤ} {ss m box L} (h : SameOutside2 μ ν ss m box L) (h' : SameOutside ν ν' box L) : SameOutside2 μ ν' ss m box L := by light_keep
theorem same_of_ss {ν ν' : ℕ → ℤ} {ss m box L} (h : SameOutside2 μ ν ss m box L) (h' : SameOutside ν ν' ss m) : SameOutside2 μ ν' ss m box L := by light_keep

structure Callees (lim : Limits) (P : Program) : Prop where
  nineFirst : NineFirstSpec lim P
  nineNext : NineNextSpec lim P
  scatter : ScatterSpec lim P
  horner : HornerSpec lim P
  lookup : RadixSpec lim P Proc.lookup 11

def Inv (μ : ℕ → ℤ) (x : QueryCoreArgs) (lo hi base i : ℕ) (σ : State) : Prop :=
  ∃ (code value : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.a, x.b, x.page, x.wd, x.ss, x.box, x.L, x.m, x.t,
      (x.terms.take (base + i)).sum, if i < (nineStrs x.m lo hi).length then 1 else 0, code, value,
      (x.m - x.t : ℕ)], μ'⟩ ∧
    SegN μ' x.ss (nineStr x.m lo hi i) ∧ SameOutside2 μ μ' x.ss x.m x.box x.L

def Mid (μ : ℕ → ℤ) (x : QueryCoreArgs) (n : ℕ) (σ : State) : Prop :=
  ∃ (more code value : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [x.a, x.b, x.page, x.wd, x.ss, x.box, x.L, x.m, x.t, (x.terms.take n).sum,
      more, code, value, (x.m - x.t : ℕ)], μ'⟩ ∧ SameOutside2 μ μ' x.ss x.m x.box x.L

theorem Inv.mid {lo hi base : ℕ} (h : Inv μ x lo hi base i σ) : Mid μ x (base + i) σ := by
  obtain ⟨code, value, μ', rfl, -, same⟩ := h
  exact ⟨_, code, value, μ', rfl, same⟩

end Query

namespace Query

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : QueryCoreArgs} {i : ℕ}

theorem count_digitsP (C : Pre lim μ x) : (digitsO x.η).count 9 = x.m := by
  rw [← card_innerSetO, C.card]

theorem low_termP (C : Pre lim μ x) (hi : i < lowCount x) :
    ∃ τ : Leaf x.L, leafAt x i = digitsT τ ∧ (P0Levels τ).card ≤ x.m ∧
      (x.terms.take (i + 1)).sum = (x.terms.take i).sum + x.A τ * x.B τ := by
  have hleaf : leafAt x i ∈ lowList x.m x.t (digitsO x.η) :=
    List.mem_map.mpr ⟨_, nineStr_mem hi, rfl⟩
  obtain ⟨τ, hlow, hτ⟩ := exists_of_mem_lowList C.card _ hleaf
  refine ⟨τ, hτ.symm, ?_, ?_⟩
  ·
    simp only [lowLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hlow
    rw [← C.card]
    exact card_P0Levels_le_of_contributes hlow.1
  have hlen : i < (lowList x.m x.t (digitsO x.η)).length := by simpa [lowList] using hi
  have hmember : (lowList x.m x.t (digitsO x.η))[i] = digitsT τ := by
    rw [hτ]
    refine Option.some.inj ((List.getElem?_eq_getElem hlen).symm.trans ?_)
    rw [lowList, List.getElem?_map, List.getElem?_eq_getElem hi, getElem_nineStrs hi]
    rfl
  rw [List.sum_take_succ_getD, QueryCoreArgs.terms, queryTerms,
    List.getD_append _ _ _ _ (by rwa [List.length_map]),
    List.getD_eq_getElem _ _ (by rwa [List.length_map]), List.getElem_map, hmember,
    leafProduct_digitsT]

variable {σ : State}

theorem segDigitsP (C : Pre lim μ x) {μ' : ℕ → ℤ}
    (same : SameOutside2 μ μ' x.ss x.m x.box x.L) :
    SegN μ' x.wd (digitsO x.η) :=
  C.segDigits.keep (by have := C.layout; light_keep [length_digitsO x.η])

section Calls

variable {lo hi : ℕ} {μ₀ : ℕ → ℤ}

theorem scatter_meetsP (K : Callees lim P) (C : Pre lim μ x) (star : Bool)
    (hstr : i < (nineStrs x.m lo hi).length) (hss : SegN μ₀ x.ss (nineStr x.m lo hi i))
    (same : SameOutside2 μ μ₀ x.ss x.m x.box x.L) (hd : d ≤ lim.depth) :
    Meets lim P Proc.scatter d [x.wd, x.ss, x.box, x.L, if star then 1 else 0] μ₀ (tScatter x.L)
      fun _ μ₁ => SegN μ₁ x.box (scatter (digitsO x.η) (starRunIf star (nineStr x.m lo hi i))) ∧
        SegN μ₁ x.ss (nineStr x.m lo hi i) ∧ SameOutside2 μ μ₁ x.ss x.m x.box x.L := by
  have hp := C.layout
  obtain ⟨hlen, -⟩ := (mem_nineStrs _).mp (nineStr_mem hstr)

  refine (K.scatter x.wd x.ss x.box x.L star (digitsO x.η) _ μ₀ (segDigitsP C same) hss
    (length_digits x) (by rw [hlen, count_digitsP C]) (by omega)
    (by omega) (by omega) (by rw [hlen]; exact (by omega)) (by omega) _
      (by omega)).mono le_rfl fun _ μ₁ ⟨hbox, same₁⟩ => ⟨hbox, ?_, same_of_box same same₁⟩
  exact hss.of_sameOutside same₁ (by omega)

theorem next_meetsP (K : Callees lim P) (C : Pre lim μ x)
    (hstr : i < (nineStrs x.m lo hi).length) (hss : SegN μ₀ x.ss (nineStr x.m lo hi i))
    (same : SameOutside2 μ μ₀ x.ss x.m x.box x.L) (hd : d ≤ lim.depth) :
    Meets lim P Proc.nineNext d [x.ss, x.m, lo, hi] μ₀ (tNineNext x.m) fun r μ₁ =>
      r = (if i + 1 < (nineStrs x.m lo hi).length then 1 else 0) ∧
        SegN μ₁ x.ss (nineStr x.m lo hi (i + 1)) ∧ SameOutside2 μ μ₁ x.ss x.m x.box x.L := by
  have hp := C.layout
  refine (K.nineNext x.ss x.m lo hi _ μ₀ hss (nineStr_mem hstr) (by omega) _ (by omega)).mono le_rfl
    fun r μ₁ ⟨hss₁, hr, same₁⟩ => ⟨?_, nineStr_succ .. ▸ hss₁, same_of_ss same same₁⟩
  rw [hr, isSome_nineNext_nineStr hstr]
  simp

end Calls

theorem lowRoundP (K : Callees lim P) (C : Pre lim μ x) (hd : d + 1 ≤ lim.depth)
    (hi : i < lowCount x) (h : Inv μ x (x.m - x.t + 1) x.m 0 i σ) :
    Ends lim P d queryLowRound σ (tScatter x.L + tHorner x.L + tNineNext x.m + 31)
      (Inv μ x (x.m - x.t + 1) x.m 0 (i + 1)) := by
  have hp := C.layout
  obtain ⟨code, value, μ₀, rfl, hss, same⟩ := h
  light_facts C C.std
  obtain ⟨τ, hτ, hfew, hsum⟩ := low_termP C hi
  light_call (scatter_meetsP K C false hi hss same (by omega)) with _ μ₁ ⟨hbox, hss₁, same₁⟩
  replace hbox : SegN μ₁ x.box (digitsT τ) := hτ ▸ hbox
  light_call (K.horner x.box x.L (digitsT τ) μ₁ hbox (length_digitsT τ) (digitsT_lt τ)
    (by omega) C.pow _ (by omega)) with _ μ' ⟨rfl, hμ'⟩
  obtain rfl : μ₁ = μ' := hμ'.symm
  rw [ofDigitList_digitsT]
  have hcode : codeT τ < 10 ^ x.L := codeT_lt τ
  light_facts C
  have hreadA : μ₁ (x.a + codeT τ) = x.A τ :=
    (C.segA.keep (μ':=μ₁)).get hfew
  have hreadB : μ₁ (x.b + codeT τ) = x.B τ :=
    (C.segB.keep (μ':=μ₁)).get hfew
  have hprod := abs_le.1 (C.prod τ)
  have hfits := abs_le.1 (C.sums (i + 1))
  rw [hsum] at hfits
  light_set ((x.terms.take i).sum + x.A τ * x.B τ) using hreadA, hreadB
  light_call (next_meetsP K C hi hss₁ same₁ (by omega)) with _ μ₂ ⟨rfl, hss₂, same₂⟩
  exact ⟨codeT τ, value, μ₂, by simp [hsum], hss₂, same₂⟩

theorem boxRoundP (K : Callees lim P) (C : Pre lim μ x) (hd : d + 1 ≤ lim.depth)
    (hi : i < boxCount x) (h : Inv μ x (x.m - x.t) (x.m - x.t) (lowCount x) i σ) :
    Ends lim P d queryBoxRound σ (tScatter x.L + tLookup x.L + tNineNext x.m + 31)
      (Inv μ x (x.m - x.t) (x.m - x.t) (lowCount x) (i + 1)) := by
  have hp := C.layout
  obtain ⟨code, value, μ₀, rfl, hss, same⟩ := h
  light_facts C.std
  obtain ⟨hbox, hsum⟩ := box_term hi
  obtain ⟨π, -, hπ⟩ := exists_of_mem_boxesOf C.t_le C.card _ hbox
  have hlen : (boxAt x i).length = x.L := by rw [boxAt, length_scatter, length_digits]
  light_call (scatter_meetsP K C true hi hss same (by omega)) with void μ₁ ⟨hbox₁, hss₁, same₁⟩
  have ds := hπ ▸ digitsC_lt π
  have hcode : ofDigitList 11 (boxAt x i) < stride x.L :=
    (ofDigitList_lt _ (show ∀ u ∈ boxAt x i, u < 11 from ds)).trans_le (hlen ▸ pow_le_stride _)
  have pow : (11:ℤ)^x.L ≤ lim.word :=
    (show (11:ℤ)^x.L ≤ (lim.space:ℤ) by exact_mod_cast (show 11^x.L ≤ lim.space by have := pow_le_stride x.L; omega)).trans C.std.space_le
  have read := (same₁ (x.page+ofDigitList 11 (boxAt x i)) (by constructor <;> omega)).trans (C.read _ hbox)
  light_call (K.lookup x.box x.L (boxAt x i) μ₁ hbox₁ hlen ds (by omega) pow _ (by omega))
    using tLookup,tHorner with _ μ' ⟨rfl, hμ'⟩
  obtain rfl : μ₁ = μ' := hμ'.symm
  have hfits := abs_le.1 (C.sums (lowCount x + (i + 1)))
  rw [hsum] at hfits
  generalize ofDigitList 11 (boxAt x i) = c at *
  generalize x.toTile.val (boxAt x i) = val at *
  light_set ((x.terms.take (lowCount x + i)).sum + val) using read, tLookup,tHorner
  light_call (next_meetsP K C hi hss₁ same₁ (by omega)) using tLookup,tHorner with _ μ₂ ⟨rfl, hss₂, same₂⟩
  exact ⟨void, c, μ₂, by simp [hsum], hss₂, same₂⟩

theorem loopP (C : Pre lim μ x) {round : Stmt} {lo hi base b : ℕ}
    (hround : ∀ i σ, i < (nineStrs x.m lo hi).length → Inv μ x lo hi base i σ →
      Ends lim P d round σ (b + 31) (Inv μ x lo hi base (i + 1)))
    (h : Inv μ x lo hi base 0 σ) :
    Ends lim P d (.while (v More =' k 1) round) σ ((nineStrs x.m lo hi).length * (b + 90) + 4)
      (Inv μ x lo hi base (nineStrs x.m lo hi).length) := by
  have hc := C.std.const_le
  have htime := Nat.mul_le_mul_left (nineStrs x.m lo hi).length
    (show 1 + 1 + 1 + 1 + (b + 31) ≤ b + 90 by omega)
  refine Ends.whileConst (Inv μ x lo hi base) (nineStrs x.m lo hi).length (b + 31) h ?round ?done
    (by simp only [Cond.cost, Expr.cost]; omega)
  case round =>
    rintro i σ hi hI
    have hends := hround i σ hi hI
    obtain ⟨code, value, μ', rfl, -⟩ := hI
    exact ⟨by simp; omega, by simp [hi], hends⟩
  case done =>
    rintro σ hI
    have hI' := hI
    obtain ⟨code, value, μ', rfl, -⟩ := hI'
    exact ⟨by simp; omega, by simp, hI⟩

theorem low_specP (K : Callees lim P) (C : Pre lim μ x) (hd : d + 1 ≤ lim.depth)
    (ht : 1 ≤ x.t) (h : Mid μ x 0 σ) :
    Ends lim P d queryLow σ
      (tNineFirst x.m + lowCount x * (tScatter x.L + tHorner x.L + tNineNext x.m + 90) + 16)
      (Mid μ x (lowCount x)) := by
  have hp := C.layout
  obtain ⟨more, code, value, μ₀, rfl, same⟩ := h
  have htm := C.t_le
  light_facts C C.std
  have hpos : 0 < lowCount x := length_nineStrs_pos (by omega) (by omega)
  light_call (K.nineFirst x.ss x.m (x.m - x.t + 1) μ₀ (by omega) (by omega) _
    (by omega)) with _ μ₁ ⟨hss, same₁⟩
  light_set 1
  refine (loopP C (b := tScatter x.L + tHorner x.L + tNineNext x.m)
    (fun i σ hi hI => lowRoundP K C hd hi hI)
    ⟨code, value, μ₁, by simp [hpos], hss, same_of_ss same same₁⟩).mono (by simp [lowCount]; omega)
    fun σ' hI => ?_
  simpa using hI.mid

theorem boxes_specP (K : Callees lim P) (C : Pre lim μ x) (hd : d + 1 ≤ lim.depth)
    (h : Mid μ x (lowCount x) σ) :
    Ends lim P d queryBoxes σ
      (tNineFirst x.m + boxCount x * (tScatter x.L + tLookup x.L + tNineNext x.m + 90) + 16)
      (Mid μ x (lowCount x + boxCount x)) := by
  have hp := C.layout
  obtain ⟨more, code, value, μ₀, rfl, same⟩ := h
  light_facts C.std
  have hpos : 0 < boxCount x := length_nineStrs_pos (by omega) le_rfl
  light_call (K.nineFirst x.ss x.m (x.m - x.t) μ₀ (by omega) (by omega) _ (by omega))
    with _ μ₁ ⟨hss, same₁⟩
  light_set 1
  exact (loopP C (b := tScatter x.L + tLookup x.L + tNineNext x.m)
    (fun i σ hi hI => boxRoundP K C hd hi hI)
    ⟨code, value, μ₁, by simp [hpos], hss, same_of_ss same same₁⟩).mono (by simp [boxCount]; omega)
    fun σ' hI => hI.mid

theorem tail_specP (K : Callees lim P) (C : Pre lim μ x) (hd : d + 1 ≤ lim.depth)
    (h : Mid μ x (lowCount x) σ) :
    Ends lim P d (queryBoxes ;; .set EncA (v Sum)) σ
      (tNineFirst x.m + boxCount x * (tScatter x.L + tLookup x.L + tNineNext x.m + 90) + 18)
      fun σ' =>
      σ'.loc 0 = x.terms.sum ∧
        SameOutside2 μ σ'.mem x.ss x.m x.box x.L := by
  light_piece (boxes_specP K C hd h) with _ ⟨more, code, value, μ', rfl, same⟩
  have hlen : x.terms.length = lowCount x + boxCount x := by
    simp [QueryCoreArgs.terms, queryTerms, lowList, boxesOf]
  have hall : (x.terms.take (lowCount x + boxCount x)).sum
      = x.terms.sum := by
    rw [← hlen,List.take_length]
  rw [hall]
  generalize x.terms.sum = result
  light_set result
  exact ⟨rfl, same⟩

end Query

open Query in

theorem queryCoreP_spec {lim : Limits} {P : Program}
    (hP : P[Proc.queryCore]? = some queryCoreBody) (K : Callees lim P) : QueryCoreSpecP lim P := by
  intro x μ C
  refine fun d hd => ⟨queryCoreBody, hP, ?_⟩
  have htm := C.t_le
  light_facts C C.std
  have hlows : (lowList x.m x.t ([] : List ℕ)).length = lowCount x := by simp [lowList]
  have hboxes : (boxesOf x.m x.t ([] : List ℕ)).length = boxCount x := by simp [boxesOf]
  unfold tQueryCore
  rw [hlows, hboxes]
  light_set (x.m - x.t : ℕ)
  have hstart : Mid μ x 0 ⟨frame (setLocal [(x.a : ℤ), x.b, x.page, x.wd, x.ss, x.box, x.L,
      x.m, x.t] Nines (x.m - x.t : ℕ)), μ⟩ := ⟨0, 0, 0, μ, by simp, .refl⟩
  light_if ht0 ht1 : x.t = 0
  · have hnone : lowCount x = 0 := by
      rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
      intro l hl
      obtain ⟨-, -, hmin, hmax⟩ := (mem_nineStrs l).mp hl
      omega
    light_piece (tail_specP K C hd (hnone ▸ hstart))
  ·
    light_piece (low_specP K C hd (by omega) hstart) with σ' hmid
    light_piece (tail_specP K C hd hmid)

end Light.Sec4.BoxTable
