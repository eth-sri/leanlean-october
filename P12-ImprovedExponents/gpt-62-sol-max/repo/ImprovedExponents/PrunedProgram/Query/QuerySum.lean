module

import ThreeSumApsp.Lang.WhileShape

public import ThreeSumApsp.Programs.Sec4.Theorem30.QuerySum
public import ImprovedExponents.PrunedProgram.Query.Contracts

@[expose] public section

/-!
# A query, once the digits of its output string are known, on pruned encodings

Upstream's `queryCore_spec` proves the routine `queryCoreBody` (procedure 53: the leaves of order
below `t`, then the boxes) under `QueryCorePre`, which holds the two encodings of the tile as full
segments.  The routine reads an encoding in one place only: a round of the first loop reads the
cell of the leaf τ that it treats (`Query.lowRound`, "sum := sum + aA[code] * aB[code]").  This
leaf contributes to the output string η and has order below `t` (`exists_of_mem_lowList`), so it
has the term `P₀` only at the inner levels of η (`card_P0Levels_le_of_contributes`), of which there
are `m` (`QueryCorePreP.card`): the pruned encodings hold its cell (`SegOn.get`).

`queryCoreP_spec` verifies both passes under `QueryCorePreP`, with `SegOn` in place of `Seg` for the
two encodings.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean` (Apache-2.0).
-/

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

namespace QueryP

open Query

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : QueryCoreArgs} {i : ℕ}

/-! ## The pure side: the terms of the sum -/

/-- The digit 9, which stands at the levels of the subset, occurs m times. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.count_digits)
theorem count_digitsP (C : QueryCorePreP lim μ x) : (digitsO x.η).count 9 = x.m := by
  rw [← card_innerSetO, C.card]

/-- Round i of the first loop treats a leaf τ and adds the product of its two numbers.  The leaf
contributes to the output string, so it has at most m symbols `P₀`: the pruned encodings hold its
cell. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.low_term)
theorem low_termP (C : QueryCorePreP lim μ x) (hi : i < lowCount x) :
    ∃ τ : Leaf x.L, leafAt x i = digitsT τ ∧ (P0Levels τ).card ≤ x.m ∧
      (x.terms.take (i + 1)).sum = (x.terms.take i).sum + x.encA τ * x.encB τ := by
  have hleaf : leafAt x i ∈ lowList x.m x.t (digitsO x.η) :=
    List.mem_map.mpr ⟨_, nineStr_mem hi, rfl⟩
  obtain ⟨τ, hlow, hτ⟩ := exists_of_mem_lowList C.card _ hleaf
  refine ⟨τ, hτ.symm, ?_, ?_⟩
  · -- the leaf contributes to η, which has m inner levels
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
    List.getD_append _ _ _ _ (by simp_all),
    List.getD_eq_getElem _ _ (by simp_all), List.getElem_map, hmember,
    leafProduct_digitsT]

variable {σ : State}

private abbrev loOf (x : QueryCoreArgs) (box : Bool) : ℕ :=
  if box then x.m - x.t else x.m - x.t + 1
private abbrev hiOf (x : QueryCoreArgs) (box : Bool) : ℕ := if box then x.m - x.t else x.m
private abbrev baseOf (x : QueryCoreArgs) (box : Bool) : ℕ := if box then lowCount x else 0
private abbrev readTime (x : QueryCoreArgs) (box : Bool) : ℕ := if box then tLookup x.L else tHorner x.L
private abbrev countOf (x : QueryCoreArgs) (box : Bool) : ℕ := (nineStrs x.m (loOf x box) (hiOf x box)).length

/-- Initialize and run either pass over the strings. -/
private theorem part_spec (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (box : Bool) (ht : box = false → 1 ≤ x.t) (h : Mid μ x (baseOf x box) σ) :
    Ends lim P d (queryPart box) σ (tNineFirst x.m + countOf x box *
      (tScatter x.L + readTime x box + tNineNext x.m + 90) + 16)
      (Mid μ x (baseOf x box + countOf x box)) := by
  obtain ⟨more, code, value, ν, rfl, same⟩ := h
  light_facts C C.std
  have htm := C.t_le
  have hb : loOf x box ≤ hiOf x box ∧ hiOf x box ≤ x.m := by
    cases box <;> simp_all [loOf, hiOf] <;> omega
  have hpos : 0 < countOf x box := length_nineStrs_pos (hb.1.trans hb.2) hb.1
  have hcost : (queryBound box).cost ≤ 3 := by cases box <;> decide
  let str := nineStr x.m (loOf x box) (hiOf x box)
  unfold queryPart
  refine Ends.callToThen (K.nineFirst x.ss x.m (loOf x box) ν (hb.1.trans hb.2) C.ss_lt _ (by omega)) ?_
    (ha := by cases box <;> light_side [queryBound, loOf, locations])
    (hT := by cases box <;> light_time [queryBound])
  rintro _ ν₁ ⟨hss, same₁⟩
  light_set (1 : ℤ) using hcost
  refine Ends.whileShape (fun i (z : ℤ × ℤ) η =>
      ⟨locations x (baseOf x box + i) (if i < countOf x box then 1 else 0) z.1 z.2, η⟩)
    (fun i _ η => SegN η x.ss (str i) ∧ SameOutside2 μ η x.ss x.m x.box x.L)
    (countOf x box) (tScatter x.L + readTime x box + tNineNext x.m + 31) (code, value) ν₁
    ⟨hss, same_of_ss same same₁⟩ ?_ (fun z η h => ⟨_, z.1, z.2, η, rfl, h.2⟩)
    (first := by simp [locations, hpos])
    (step := by intros; simp_all [locations]; omega)
    (stop := by intros; simp [locations]; omega)
    (hT := by
      have := Nat.mul_le_mul_left (countOf x box)
        (show 4 + (tScatter x.L + readTime x box + tNineNext x.m + 31) ≤
          tScatter x.L + readTime x box + tNineNext x.m + 90 by omega)
      simp only [Cond.cost, Expr.cost, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.reduceAdd]
      omega)
  rintro i ⟨code, value⟩ η hi ⟨hss, same⟩
  simp only [ite_eq_left hi]
  have hstr := nineStr_mem hi
  have hlen : (str i).length = x.m := length_of_mem_nineStrs hstr
  have hwd := seg_of_same same C.segDigits (by simpa [length_digits] using C.ss_wd)
    (by simpa [length_digits] using C.box_wd)
  unfold queryRound
  light_call (K.scatter x.wd x.ss x.box x.L box _ (str i) η hwd hss (length_digits x)
    (by rw [count_digitsP C]; exact hlen) C.box_wd (by rw [hlen]; omega)
    C.wd_lt (hlen ▸ C.ss_lt) C.box_lt _ (by omega)) using locations with trash ξ ⟨hb, same₂⟩
  have hs := hss.of_sameOutside same₂ (by rw [hlen]; omega)
  have hk := same_of_box same same₂
  refine Ends.pieceThen (T₁ := readTime x box + 16)
    (R := fun s => ∃ c v, s = ⟨locations x (baseOf x box + (i + 1)) 1 c v, ξ⟩) ?_ ?_
    (by cases box <;> light_time [queryBound, readTime])
  · cases box
    · simp only [baseOf, readTime, Bool.false_eq_true, ite_false, Nat.zero_add]
      obtain ⟨τ, hτ, hfew, hsum⟩ := low_termP C hi
      have hbox : SegN ξ x.box (digitsT τ) := hτ ▸ hb
      unfold queryAdd
      light_call (K.horner x.box x.L (digitsT τ) ξ hbox (length_digitsT τ) (digitsT_lt τ)
        C.box_lt C.pow _ (by omega)) using locations, readTime with _ ν' ⟨rfl, hν'⟩
      obtain rfl : ξ = ν' := hν'.symm
      rw [ofDigitList_digitsT]
      have hcode := codeT_lt τ
      have ha := (segOn_of_same hk C.segA C.ss_aA C.box_aA).get hfew
      have hb' := (segOn_of_same hk C.segB C.ss_aB C.box_aB).get hfew
      have hp := abs_le.1 (C.prod τ)
      have hfits := abs_le.1 (C.sums (i + 1))
      rw [hsum] at hfits
      light_set ((x.terms.take i).sum + x.encA τ * x.encB τ) using locations, ha, hb'
      exact ⟨codeT τ, value, by simp [locations, hsum]⟩
    · simp only [baseOf, readTime, ite_true]
      obtain ⟨hm, hsum⟩ := box_term hi
      obtain ⟨π, -, hπ⟩ := exists_of_mem_boxesOf C.t_le C.card _ hm
      have hlen : (boxAt x i).length = x.L := by rw [boxAt, length_scatter, length_digits]
      unfold queryAdd
      light_call (K.lookup x.tr x.root x.box x.L x.T (boxAt x i) ξ
        (seg_of_same hk C.segT C.ss_tr C.box_tr) hb hlen (hπ ▸ digitsC_lt π) (C.walk _ hm)
        C.tr_lt C.box_lt _ (by omega)) using locations, readTime with _ ν' ⟨rfl, hν'⟩
      obtain rfl : ξ = ν' := hν'.symm
      have hfits := abs_le.1 (C.sums (lowCount x + (i + 1)))
      rw [hsum] at hfits
      generalize trieLookup x.T x.root (boxAt x i) = val at *
      light_set ((x.terms.take (lowCount x + i)).sum + val) using locations
      exact ⟨trash, val, by simp [locations, hsum]⟩
  · rintro _ ⟨c, val, rfl⟩
    refine Ends.callTo (K.nineNext x.ss x.m (loOf x box) (hiOf x box) (str i) ξ hs hstr C.ss_lt _ (by omega)) ?_
      (ha := by cases box <;> light_side [locations, queryBound, loOf, hiOf])
      (hT := by cases box <;> light_time [queryBound, readTime])
    rintro r ν₂ ⟨hss₂, hr, same₃⟩
    rw [isSome_nineNext_nineStr hi] at hr
    refine ⟨(c, val), ν₂, by simp [locations, hr], ?_, same_of_ss hk same₃⟩
    simpa only [str, nineStr_succ] using hss₂

/-- The boxes, and the result. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (Query.tail_spec)
theorem tail_specP (K : Callees lim P) (C : QueryCorePreP lim μ x) (hd : d + 1 ≤ lim.depth)
    (h : Mid μ x (lowCount x) σ) :
    Ends lim P d (queryPart true ;; .set EncA (v Sum)) σ
      (tNineFirst x.m + boxCount x * (tScatter x.L + tLookup x.L + tNineNext x.m + 90) + 18)
      fun σ' =>
      σ'.loc 0 = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) ∧
        SameOutside2 μ σ'.mem x.ss x.m x.box x.L := by
  -- the boxes
  light_piece (part_spec K C hd true (by simp) h) using countOf, loOf, hiOf, readTime, boxCount with _ ⟨more, code, value, μ', rfl, same⟩
  have hlen : x.terms.length = lowCount x + boxCount x := by
    simp [QueryCoreArgs.terms, queryTerms, lowList, boxesOf]
  have hall : (x.terms.take (lowCount x + boxCount x)).sum
      = trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) := by
    rw [← hlen, List.take_length, QueryCoreArgs.terms, trieQuery]
  change Ends _ _ _ _ ⟨locations x (lowCount x + boxCount x) more code value, μ'⟩ _ _
  simp only [locations]
  rw [hall]
  generalize trieQuery x.m x.t (arrT x.encA) (arrT x.encB) x.T x.root (digitsO x.η) = result
  -- return sum
  light_step using countOf, loOf, hiOf, readTime, boxCount
  trivial

end QueryP

open Query QueryP in
/-- **queryCore** meets its specification on pruned encodings: upstream's routine, under the
assumption that the two encodings are right at the leaves with at most `m` symbols `P₀` only. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/QuerySum.lean (queryCore_spec)
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
  -- nines := m - t
  light_set (x.m - x.t : ℕ)
  have hstart : Mid μ x 0 ⟨frame (setLocal [(x.aA : ℤ), x.aB, x.tr, x.root, x.wd, x.ss, x.box, x.L,
      x.m, x.t] Nines (x.m - x.t : ℕ)), μ⟩ := ⟨0, 0, 0, μ, by simp [locations], .refl⟩
  -- if t = 0 there are no leaves of order below t
  light_if ht0 ht1 : x.t = 0
  · have hnone : lowCount x = 0 := by
      rw [List.length_eq_zero_iff, List.eq_nil_iff_forall_not_mem]
      intro l hl
      obtain ⟨-, -, hmin, hmax⟩ := (mem_nineStrs l).mp hl
      omega
    light_piece (tail_specP K C hd (hnone ▸ hstart))
  · -- the leaves of order below t, then the boxes
    light_piece (part_spec K C hd false (by omega) hstart) using countOf, loOf, hiOf, readTime, lowCount with σ' hmid
    simp only [baseOf, Bool.false_eq_true, ite_false, Nat.zero_add] at hmid
    light_piece (tail_specP K C hd hmid) using countOf, loOf, hiOf, readTime, lowCount with _ h
    exact h

end Light.Sec4
