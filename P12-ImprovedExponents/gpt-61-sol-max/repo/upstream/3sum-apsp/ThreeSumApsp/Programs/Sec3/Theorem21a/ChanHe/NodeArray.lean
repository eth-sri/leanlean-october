/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Auto
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.Buckets
public import ThreeSumApsp.Programs.Sec3.Theorem21a.ChanHe.NodeMemory

/-!
# The reduction from 3SUM to Convolution-3SUM: the array of a node

Theorem 21(a), after [CH20, Theorem 5.1].
nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr) writes the first `8 m²` cells of the
one-array instance of the node `(S₁, S₂, S₃, M)` (`ChanHe.Node.oneArray`) to `y`
(`nodeArray_spec`).  The array consists of c = 2m² groups of four cells; cell t of group i is the
cell y + 4i + t.

* With `W = 2V + 1` and `G = 3W + 1` the padding pattern `10G, W + G, W + 3G, -W + 4G` (`padVal`) is
  written to all groups (`pad_ends`).
* Then, for each of the three sets, a pass (`placeStmt`, `place_ends`) computes the remainders of
  the numbers sg · x, where x runs through the set and sg is 1 for the first two sets and -1 for the
  third; counts them in the count table; writes sg · x + g, for every x whose remainder r has the
  count 1, to cell off of group r (and of group r + M, for the third set; `placeRound_ends`,
  `PlaceInv`); and removes the counts again.  Here g is G, 3G, 4G and off is 1, 2, 3.
* In terms of the arrays of the reduction (`place_arr`): afterwards cell off of group i holds entry
  i of the array of the set, plus g (`place_col` for the first two sets, `place_colZ` for the
  third).
* The four kinds of cells make up the one-array instance (`oneArray_of_cells`); the parts are put
  together in `nodeArrayBody_ends`.

The three passes are the same piece of text, which reads its parameters from local variables.  It is
not a procedure of its own, so that the depth of calls is the one that the specification allows for.

From other files: `keys M L` is the list of the remainders of the numbers of L, as natural numbers;
`arr S M pd r` is the element of S with the remainder r if there is exactly one, and the padding
value pd otherwise; `arrZ` is the same for the negatives of S, repeated at r + M; `BucketPre` is
what coll and heavy assume about a set and the count table; `Counted` says that the remainders stand
at the free pointer and that the table holds how often each occurs.
-/

@[expose] public section

namespace Light.Sec3.ChanHe

open ThreeSumApsp ThreeSumApsp.ChanHe ThreeSumApsp.Spec.ChanHeArray

variable {lim : Limits} {P : Program} {d : ℕ}

/-! ## The local variables -/


/-- The arguments of nodeArray. -/
structure ArrArgs where
  (Mo s₁ l₁ s₂ l₂ s₃ l₃ V m y cnt fr : ℕ)

/-- The padding pattern: what cell t of a group holds before the passes. -/
def padVal (V t : ℕ) : ℤ :=
  if t = 0 then 10 * (6 * V + 4) else if t = 1 then (2 * V + 1) + (6 * V + 4)
  else if t = 2 then (2 * V + 1) + 3 * (6 * V + 4) else -(2 * V + 1) + 4 * (6 * V + 4)

/-- The scratch variables of the padding loop and of a pass: counter, address, remainder, value,
result of a call, and the free pointer behind the remainders. -/
structure ArrScratch where
  (idx ad key val res fr2 : ℤ)

/-- The list of the local variables of nodeArray, once the constants have been computed. -/
abbrev arrLocals (a : ArrArgs) (x : ArrScratch) (sg g : ℤ) (s len off δ : ℕ) : List ℤ :=
  [a.Mo, a.s₁, a.l₁, a.s₂, a.l₂, a.s₃, a.l₃, a.V, a.m, a.y, a.cnt, a.fr, 2 * a.V + 1, 6 * a.V + 4,
    x.idx, x.ad, x.key, x.val, x.res, 2 * (a.m * a.m), sg, g, s, len, off, δ, x.fr2,
    padVal a.V 0, padVal a.V 1, padVal a.V 2, padVal a.V 3]

/-! ## The padding pattern -/

/-- For i < 2m²: the four cells of group i become the padding pattern. -/
def padStmt : Stmt :=
  .for 14 (v 19) (
    .store (v 9 +' k 4 *' v 14) (v 27) ;;
    .store (v 9 +' k 4 *' v 14 +' k 1) (v 28) ;;
    .store (v 9 +' k 4 *' v 14 +' k 2) (v 29) ;;
    .store (v 9 +' k 4 *' v 14 +' k 3) (v 30))

/-- The memory before group j is written: the groups below j hold the pattern p, and no cell outside
the c groups has changed. -/
def PadInv μ y c (p : Light.Memory) j μ' :=
  (∀ i < j, ∀ t < 4, μ' (y + 4 * i + t) = p t) ∧ SameOutside μ μ' y (4 * c)

/-- One more group. -/
theorem PadInv.succ {μ μ'} {y c j} {p} (h : PadInv μ y c p j μ') (hj : j < c) :
    PadInv μ y c p (j + 1) (Function.update (Function.update (Function.update (Function.update μ'
      (y + 4 * j) (p 0)) (y + 4 * j + 1) (p 1)) (y + 4 * j + 2) (p 2)) (y + 4 * j + 3) (p 3)) := by
  refine ⟨fun i hi t ht => ?_, (((h.2.update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩
    _).update ⟨by omega, by omega⟩ _).update ⟨by omega, by omega⟩ _⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hlt | rfl
  ram_safe

/-- **The padding pattern** is written to all groups. -/
theorem pad_ends {μ} {a} (hw : (lim.space : ℤ) ≤ lim.word)
    (hy : a.y + 4 * (2 * (a.m * a.m)) ≤ lim.space) {x} {sg g}
    {s len off δ} :
    Ends lim P d padStmt ⟨frame (arrLocals a x sg g s len off δ), μ⟩ (42 * (2 * (a.m * a.m)) + 6)
      fun σ' => ∃ μ', PadInv μ a.y (2 * (a.m * a.m)) (padVal a.V) (2 * (a.m * a.m)) μ' ∧
        σ' = ⟨frame (arrLocals a { x with idx := 2 * (a.m * a.m) } sg g s len off δ),
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
  case done => aesop

/-! ## One pass over a set -/

/-- A round of the loop of a pass: key := mem[fr + j]; if mem[cnt + key] = 1 then
sg * mem[s + j] + g is written to the cells y + 4 key + off and y + 4 key + off + δ. -/
def placeRound  :=
  .set 16 (M (v 11 +' v 14)) ;;
  .ite (M (v 10 +' v 16) =' k 1)
    (.set 15 (v 9 +' k 4 *' v 16 +' v 24) ;;
     .set 17 (v 20 *' M (v 22 +' v 14) +' v 21) ;;
     .store (v 15) (v 17) ;;
     .store (v 15 +' v 25) (v 17))
    .skip

/-- The loop of a pass: a round for each j < len. -/
def placeLoop : Stmt := .for 14 (v 23) placeRound

/-- One pass.  The remainders of the numbers sg · x go to the cells from the free pointer and are
counted; the loop writes sg · x + g for every x whose remainder has the count 1; the counts are
removed. -/
def placeStmt (pResid pTally : ℕ)  :=
  .set 26 (v 11 +' v 23) ;;
  .call pResid [v 23, v 22, v 20, v 0, v 11, v 26] 18 ;;
  .call pTally [v 23, v 11, v 10, k 1] 18 ;;
  placeLoop ;;
  .call pTally [v 23, v 11, v 10, k 0 -' k 1] 18

/-- The time of a pass over len numbers: remainders, counting, the loop, and removing the counts. -/
def tPlace len V := tResid len V + 2 * tTally len + 45 * len + 32

/-- The cells that a pass may write: the cells y + 4r + off and y + 4r + off + δ for r < M. -/
def PlaceCell y off δ Mo b := ∃ r < Mo, b = y + 4 * r + off ∨ b = y + 4 * r + off + δ

/-- The memory μ' before element j of a pass is looked at.  μ is the memory before the loop, K the
list of the remainders, and val r what the cells of the remainder r are to hold.  The cells of the
remainders that have the count 1 and occur among the first j remainders hold their values, and no
other cell has changed. -/
structure PlaceInv (μ μ' : Light.Memory) (y off δ Mo : ℕ) (K : List ℕ) (val : Light.Memory) (j : ℕ) : Prop where
  cells : ∀ r < Mo, ∀ e, e = 0 ∨ e = δ → μ' (y + 4 * r + off + e) =
    if K.count r = 1 ∧ r ∈ K.take j then val r else μ (y + 4 * r + off + e)
  rest : SameOn (fun b => ¬ PlaceCell y off δ Mo b) μ μ'

namespace PlaceInv

variable {μ μ' : Light.Memory} {y off δ Mo j : ℕ} {K : List ℕ} {val : Light.Memory}

/-- Before the first element. -/
theorem zero : PlaceInv μ μ y off δ Mo K val 0 := ⟨fun r _ e _ => by simp, .refl⟩

/-- The first j + 1 remainders are the first j and remainder number j. -/
theorem mem_take_succ hj r :
    r ∈ K.take (j + 1) ↔ r ∈ K.take j ∨ r = K[j] := by
  rw [List.take_succ_eq_append_getElem hj, List.mem_append, List.mem_singleton]

variable (h : PlaceInv μ μ' y off δ Mo K val j)

include h in
/-- An element whose remainder has the count 1 is written to its two cells. -/
theorem succ_one  hj (hlt : K[j] < Mo)
    (hone : K.count K[j] = 1) (hδ : δ = 0 ∨ 4 * Mo ≤ δ) :
    PlaceInv μ (Function.update (Function.update μ' (y + 4 * K[j] + off) (val K[j]))
      (y + 4 * K[j] + off + δ) (val K[j])) y off δ Mo K val (j + 1) := by
  refine ⟨fun r hr e he => ?_, fun b hb => ?_⟩
  · by_cases hrK : r = K[j]
    · grind [mem_take_succ]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), h.cells r hr e he]
      simp only [mem_take_succ hj, hrK, or_false]
  · ram_aesop [Light.Sec3.ChanHe.PlaceCell]

include h in
/-- An element whose remainder does not have the count 1 is passed over. -/
theorem succ_many  hj
    (hmany : K.count K[j] ≠ 1) : PlaceInv μ μ' y off δ Mo K val (j + 1) := by
  refine ⟨fun r hr e he => ?_, h.rest⟩
  rw [h.cells r hr e he]
  by_cases hrK : r = K[j]
  · subst hrK
    simp [hmany]
  · simp only [mem_take_succ hj, hrK, or_false]

/-- After the last element. -/
theorem done (h : PlaceInv μ μ' y off δ Mo K val K.length) {r} (hr : r < Mo) {e}
    (he : e = 0 ∨ e = δ) : μ' (y + 4 * r + off + e) =
      if K.count r = 1 then val r else μ (y + 4 * r + off + e) := by
  ram_safe

end PlaceInv

/-- What a pass assumes: what coll and heavy assume about the set and the count table; sg is 1
or -1; the array of ylen cells from y lies below the free pointer, apart from the set and the table,
and has room for the cells that the pass writes; off is the number of a cell in its group; the
second cell is the first one (δ = 0) or lies behind the first M groups; and sg · x + g fits in a
word. -/
structure PassPre (lim : Limits) (μ : Light.Memory) (d : ℕ) (a : ArrArgs) (sg g : ℤ) (s off δ cap ylen : ℕ)
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

section

variable {μ μ₀ : Light.Memory} {a : ArrArgs} {sg g : ℤ} {s off δ cap ylen : ℕ} {L : List ℤ} {K : List ℕ}
  {val : Light.Memory}

variable (H : PassPre lim μ₀ d a sg g s off δ cap ylen L)

include H in
/-- A cell that a pass may write lies in the array. -/
theorem PassPre.placeCell_lt {b}
    (hb : PlaceCell a.y off δ a.Mo b) : a.y ≤ b ∧ b < a.y + ylen := by
  obtain ⟨r, hr, hb⟩ := hb
  light_facts H
  omega

variable (hlen : K.length = L.length) (hlt : ∀ q ∈ K, q < a.Mo) (counted : Counted μ a.fr a.cnt cap K)
    (hL : Seg μ s L) (hval : ∀ j (hK : j < K.length) (hj : j < L.length), K.count K[j] = 1 →
      sg * L[j] + g = val K[j])

include H hlen hlt counted hL hval in
/-- **A round of the loop of a pass** looks at element j.  μ₀ is the memory at the start of the pass
(of H only the layout and the limits are used), μ the memory at the start of the loop, when the
remainders K have been counted, and μ' the memory before the round. -/
theorem placeRound_ends
     (x : ArrScratch) {j} (hj : j < L.length) {μ'}
    (inv : PlaceInv μ μ' a.y off δ a.Mo K val j) :
    Ends lim P d placeRound
      ⟨frame (arrLocals a { x with idx := j } sg g s L.length off δ), μ'⟩ 37 fun σ' =>
      ∃ (x' : ArrScratch) (μ'' : Light.Memory),
        σ' = ⟨frame (arrLocals a { x' with idx := j } sg g s L.length off δ), μ''⟩ ∧
        PlaceInv μ μ'' a.y off δ a.Mo K val (j + 1) := by
  light_facts H H.bucket H.bucket.ok
  have hcells := H.bucket.ok.cells
  simp only [collNeed] at hcells
  have hjK := hlen ▸ hj
  have hkey_lt := hlt _ (List.getElem_mem hjK)
  -- The three cells that the round reads lie outside the array, so they have not changed.
  have hout : ∀ b, b < a.y ∨ a.y + ylen ≤ b → μ' b = μ b := fun b hb =>
    inv.rest b fun ⟨r, hr, hEq⟩ => by omega

  have hcount : μ' (a.cnt + K[j]) = (K.count K[j] : ℤ) :=
    (hout _ (by omega)).trans (counted.counts _ (by omega))
  have hread := (hout _ (by omega)).trans (hL j hj)
  -- The value that is written fits in a word.

  have  := abs_le.1 (by
    rcases H.sign with rfl | rfl <;> simpa using H.bucket.bounded.getElem hj
   : |sg * L[j]| ≤ (a.V : ℤ))

  have  := abs_le.1 (le_refl |g|)
  -- key := mem[fr + j]
  light_set K[j] using ((hout _ (by omega)).trans (counted.keys.getElem hjK))
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

include H hlen hlt counted hL hval in
/-- **The loop of a pass.**  μ₀ is the memory at the start of the pass, μ the memory at the start of
the loop. -/
theorem placeLoop_ends  x :
    Ends lim P d placeLoop ⟨frame (arrLocals a x sg g s L.length off δ), μ⟩ (45 * L.length + 6)
      fun σ' => ∃ (x' : ArrScratch) (μ' : Light.Memory),
        σ' = ⟨frame (arrLocals a x' sg g s L.length off δ), μ'⟩ ∧
        PlaceInv μ μ' a.y off δ a.Mo K val L.length := by
  have  := sq_add_le_word H.bucket.ok.word
  have  : (0 : ℤ) ≤ (L.length : ℤ) * L.length := by positivity
  -- for j < len; the scratch variables hold anything
  exact Ends.forShape
    _
    _ L.length 37 x .zero
    (fun j x' μ' hj inv => placeRound_ends H hlen hlt counted hL hval x' hj inv)
    fun x' μ' inv => ⟨_, μ', rfl, inv⟩

/-- **One pass.**  val r is what the cells of the remainder r are to hold if r has the count 1. -/
theorem place_ends {pResid pTally} (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (H : PassPre lim μ d a sg g s off δ cap ylen L)
    (hval : ∀ j (hj : j < L.length),
      (keys a.Mo (L.map (sg * ·))).count (sg * L[j] % a.Mo).toNat = 1 →
        sg * L[j] + g = val (sg * L[j] % a.Mo).toNat) x :
    Ends lim P d (placeStmt pResid pTally) ⟨frame (arrLocals a x sg g s L.length off δ), μ⟩
      (tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : Light.Memory), σ' = ⟨frame (arrLocals a x' sg g s L.length off δ), μ'⟩ ∧
        (∀ r < a.Mo, ∀ e, e = 0 ∨ e = δ → μ' (a.y + 4 * r + off + e) =
          if (keys a.Mo (L.map (sg * ·))).count r = 1 then val r
          else μ (a.y + 4 * r + off + e)) ∧
        SameOn (fun b => b < a.fr ∧ ¬ PlaceCell a.y off δ a.Mo b) μ μ' := by
  have C := H.bucket
  simp only [tPlace]
  have hlen : (keys a.Mo (L.map (sg * ·))).length = L.length := by simp
  have hlt := keys_lt C.modulus_pos (L.map (sg * ·))

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
    fun j _ hj hone => by simpa [keys] using hval j hj (by simpa [keys] using hone)
    { x with res := res, fr2 := (a.fr + L.length : ℕ) }) with _ ⟨x₃, μ₃, rfl, inv⟩
  have same₃ : SameOutside μ₂ μ₃ a.y ylen := SameOn.mono inv.rest fun b hb hcell => by
    have := H.placeCell_lt hcell
    omega
  -- tally(len, fr, cnt, -1)
  light_call (C.uncount_meets hT hlen hlt (counted.of_sameOutside same₃ H.belowArr H.apartTable))
    with res' μ₄ ⟨zero₄, same₄⟩
  refine ⟨{ x₃ with res := res' }, μ₄, rfl, fun r hr e he => ?_, ?_⟩
  · rw [← hlen] at inv
    rw [same₄ _ (by omega), inv.done hr he, kept₂ _ (by omega)]
  · exact sameOn_of_zeroAt ((kept₂.then inv.rest fun b hb => ⟨⟨hb.1.1, hb.2⟩, hb.1.2⟩).then same₄
      fun b hb => ⟨hb, hb.2⟩) C.zero zero₄

/-- One pass, in terms of the array `arr` of the set of the numbers sg · x: if the cells hold pd + g
before, for a padding value pd, they hold the entries of the array, plus g, afterwards. -/
theorem place_arr {pResid pTally} (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (H : PassPre lim μ d a sg g s off δ cap ylen L) (hnd : L.Nodup) {pd}
    (hpad : ∀ r < a.Mo, ∀ e, e = 0 ∨ e = δ → μ (a.y + 4 * r + off + e) = pd + g)
     x :
    Ends lim P d (placeStmt pResid pTally) ⟨frame (arrLocals a x sg g s L.length off δ), μ⟩
      (tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : Light.Memory), σ' = ⟨frame (arrLocals a x' sg g s L.length off δ), μ'⟩ ∧
        (∀ r < a.Mo, ∀ e, e = 0 ∨ e = δ → μ' (a.y + 4 * r + off + e) =
          arr (L.map (sg * ·)).toFinset a.Mo pd r + g) ∧
        SameOn (fun b => b < a.fr ∧ ¬ PlaceCell a.y off δ a.Mo b) μ μ' := by

  have hnd' : (L.map (sg * ·)).Nodup := hnd.map fun u w huw => by
    ram_arith
  refine (place_ends hR hT H (val := fun r => arr (L.map (sg * ·)).toFinset a.Mo pd r + g)
    (fun j hj hone => ?_) x).mono le_rfl ?_
  · have h := arr_of_count_eq_one H.bucket.modulus_pos hnd' pd (j := j) (by simpa using hj)
    simp only [List.getElem_map] at h
    rw [h hone]
  · rintro _ ⟨x', μ', rfl, hcells, hrest⟩
    refine ⟨x', μ', rfl, fun r hr e he => ?_, hrest⟩
    grind [arr_of_count_ne_one]

end

/-! ## A pass, in terms of the cells number off of the groups -/

/-- No cell below the free pointer has changed, except cell t of the c groups from y. -/
abbrev KeptCol μ μ' fr y c t :=
  SameOn (fun b => b < fr ∧ ∀ i < c, b ≠ y + 4 * i + t) μ μ'

/-- A cell of another kind has not changed. -/
def KeptCol.cell {μ μ'} {fr y c t} (h : KeptCol μ μ' fr y c t) {i t'}
    (hb : y + 4 * i + t' < fr) (ht : t < 4 := by omega) (ht' : t' < 4 := by omega)
    (hne : t' ≠ t := by omega) :=
  h _ ⟨hb, fun _ _ => by omega⟩

/-- The cells outside the array have not changed either. -/
def KeptCol.keptBut {μ μ' μ''} {fr y c t} (h : KeptCol μ' μ'' fr y c t)
    (hk : KeptBut μ μ' fr y (4 * c)) (ht : t < 4 := by omega) :=
  hk.then h fun b hb => ⟨hb, hb.1, fun i hi => by omega⟩

section

variable {μ : Light.Memory} {a : ArrArgs} {g pd : ℤ} {s off cap c : ℕ} {L : List ℤ} {pResid pTally : ℕ}

variable (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)

include hR hT in
/-- **A pass for the first or the second set**: if cell off of each of the c groups holds pd + g
before, then afterwards cell off of group i holds entry i of the array of the set with the padding
value pd, plus g, and no other cell below the free pointer has changed. -/
theorem place_col
    (H : PassPre lim μ d a 1 g s off 0 cap (4 * c) L) (hnd : L.Nodup)
    (hpad : ∀ i < c, μ (a.y + 4 * i + off) = pd + g) x :
    Ends lim P d (placeStmt pResid pTally) ⟨frame (arrLocals a x 1 g s L.length off 0), μ⟩
      (tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : Light.Memory), σ' = ⟨frame (arrLocals a x' 1 g s L.length off 0), μ'⟩ ∧
        (∀ i < c, μ' (a.y + 4 * i + off) = arr L.toFinset a.Mo pd i + g) ∧
        KeptCol μ μ' a.fr a.y c off := by
  light_facts H
  refine (place_arr hR hT H hnd (pd := pd) (fun r hr e he => ?_) x).mono le_rfl ?_
  · ram_grind
  rintro _ ⟨x', μ', rfl, hcells, hrest⟩
  refine ⟨x', μ', rfl, fun i hi => ?_, SameOn.mono hrest fun b hb => ⟨hb.1, ?_⟩⟩
  · by_cases hiM : i < a.Mo
    · simp_all
    · rw [hrest _ ⟨by omega, fun ⟨r, hr, hEq⟩ => by omega⟩,
        arr_of_le H.bucket.modulus_pos _ _ (by omega), hpad i hi]
  · rintro ⟨r, hr, hEq⟩
    exact hb.2 r (by omega) (by omega)

include hR hT in
/-- **The pass for the third set**: if cell off of each of the c groups holds -(2V + 1) + g before,
then afterwards cell off of group i holds entry i of the third array of the node, plus g, and no
other cell below the free pointer has changed. -/
theorem place_colZ
    (H : PassPre lim μ d a (-1) g s off (4 * a.Mo) cap (4 * c) L) (hnd : L.Nodup)
    (hpad : ∀ i < c, μ (a.y + 4 * i + off) = -(2 * a.V + 1) + g) x :
    Ends lim P d (placeStmt pResid pTally)
      ⟨frame (arrLocals a x (-1) g s L.length off (4 * a.Mo)), μ⟩
      (tPlace L.length a.V) fun σ' =>
      (∀ i < c, σ'.mem (a.y + 4 * i + off) = arrZ L.toFinset a.Mo a.V i + g) ∧
        KeptCol μ σ'.mem a.fr a.y c off := by
  light_facts H

  refine (place_arr hR hT H hnd (pd := -(2 * a.V + 1)) (fun r hr e he => ?_) x).mono le_rfl ?_
  · rcases he with rfl | rfl
    · exact hpad r (by omega)
    · rw [show a.y + 4 * r + off + 4 * a.Mo = a.y + 4 * (r + a.Mo) + off by ring]
      exact hpad _ (by omega)
  rintro _ ⟨x', μ', rfl, hcells, hrest⟩
  rw [(by
    ext u
    simp
   : (L.map (-1 * ·)).toFinset = L.toFinset.image fun u => -u)] at hcells
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

end

/-! ## The routine -/

/-- The constants: W = 2V + 1, G = 3W + 1, the number 2m² of groups, and the padding pattern. -/
def arrConsts  :=
  .set 12 (k 2 *' v 7 +' k 1) ;;
  .set 13 (k 3 *' v 12 +' k 1) ;;
  .set 19 (k 2 *' (v 8 *' v 8)) ;;
  .set 27 (k 10 *' v 13) ;;
  .set 28 (v 12 +' v 13) ;;
  .set 29 (v 12 +' k 3 *' v 13) ;;
  .set 30 (k 4 *' v 13 -' v 12)

/-- The pass for the first set: x + G goes to cell 1 of the group of its remainder. -/
def arrPass₁ (pResid pTally : ℕ)  :=
  .set 20 (k 1) ;;
  .set 21 (v 13) ;;
  .set 22 (v 1) ;;
  .set 23 (v 2) ;;
  .set 24 (k 1) ;;
  .set 25 (k 0) ;;
  placeStmt pResid pTally

/-- The pass for the second set: x + 3G goes to cell 2 of the group of its remainder.  The sign 1
and the distance 0 are as the first pass left them. -/
def arrPass₂ (pResid pTally : ℕ)  :=
  .set 21 (k 3 *' v 13) ;; .set 22 (v 3) ;; .set 23 (v 4) ;; .set 24 (k 2) ;;
  placeStmt pResid pTally

/-- The pass for the third set: -x + 4G goes to cell 3 of the groups r and r + M, where r is the
remainder of -x. -/
def arrPass₃ (pResid pTally : ℕ)  :=
  .set 20 (k 0 -' k 1) ;; .set 21 (k 4 *' v 13) ;; .set 22 (v 5) ;; .set 23 (v 6) ;;
  .set 24 (k 3) ;; .set 25 (k 4 *' v 0) ;;
  placeStmt pResid pTally

/-- nodeArray(M, s₁, l₁, s₂, l₂, s₃, l₃, V, m, y, cnt, fr), over the procedures number pResid and
pTally. -/
def nodeArrayBody pResid pTally :=
  arrConsts ;; padStmt ;; arrPass₁ pResid pTally ;; arrPass₂ pResid pTally ;;
  arrPass₃ pResid pTally

/-- What nodeArray assumes, apart from the three sets: the modulus, the count table, the place of
the array, and the limits. -/
structure ArrPre (lim : Limits) (μ : Light.Memory) (d n : ℕ) (a : ArrArgs) : Prop where
  modulus_pos : 1 ≤ a.Mo
  modulus_le : a.Mo ≤ a.m * a.m
  zero : ZeroAt μ a.cnt (a.m * a.m)
  belowTable : a.cnt + a.m * a.m ≤ a.fr
  belowArr : a.y + 4 * (2 * (a.m * a.m)) ≤ a.fr
  apartTable : Apart a.y (4 * (2 * (a.m * a.m))) a.cnt (a.m * a.m)
  ok : (nodeArrayNeed n a.V a.m).Ok lim a.fr d

/-- What nodeArray assumes about one of the three sets, given as the list L at s. -/
structure ArrSet (μ : Light.Memory) (n : ℕ) (a : ArrArgs) (s : ℕ) (L : List ℤ) : Prop where
  list : Seg μ s L
  nodup : L.Nodup
  bounded : AbsLe L a.V
  le : L.length ≤ n
  below : s + L.length ≤ a.fr
  apartTable : Apart s L.length a.cnt (a.m * a.m)
  apartArr : Apart a.y (4 * (2 * (a.m * a.m))) s L.length

section

variable {μ μ' : Light.Memory} {n : ℕ} {a : ArrArgs} {s : ℕ} {L : List ℤ} {pResid pTally : ℕ}

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
  simpa using mul_le_word (y := 1) h.ok.word
    (Nat.one_le_pow _ _ (by omega)) (by omega) le_rfl

/-- What a pass assumes, from what nodeArray assumes. -/
theorem ArrPre.pass (h : ArrPre lim μ d n a) (hS : ArrSet μ n a s L) {sg g} {off δ}
    (hsg : sg = 1 ∨ sg = -1) (hoff : off < 4) (hδ : δ = 0 ∨ δ = 4 * a.Mo)
    (hg₀ : 0 ≤ g) (hg : g ≤ 32 * ((a.V : ℤ) + 1)) :
    PassPre lim μ d a sg g s off δ (a.m * a.m) (4 * (2 * (a.m * a.m))) L := by
  have hM := h.modulus_le
  have  := h.word_le
  have hle := hS.le
  have  := abs_of_nonneg hg₀
  exact
    { bucket :=
        { h with
          modulus_le := hM
          bounded := hS.bounded
          list := hS.list

          belowList := hS.below

          apart := hS.apartTable
          ok := h.ok.mono (wordNeed_mono hle hM) (by simp_all [collNeed, nodeArrayNeed])
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
  have  := h.word_le
  light_facts h h.ok
  light_block [Light.Sec3.ChanHe.arrConsts, Light.Sec3.ChanHe.arrLocals, padVal]

variable (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally)
    (h : ArrPre lim μ d n a)

include hR hT h in
/-- **The pass for the first set.** -/
theorem arrPass₁_ends  (hS : ArrSet μ n a a.s₁ L) (hl : a.l₁ = L.length)
    (hpad : ∀ i < 2 * (a.m * a.m), μ (a.y + 4 * i + 1) = padVal a.V 1) {x}
    {sg g} {s len off δ} :
    Ends lim P d (arrPass₁ pResid pTally) ⟨frame (arrLocals a x sg g s len off δ), μ⟩
      (12 + tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : Light.Memory),
        σ' = ⟨frame (arrLocals a x' 1 (6 * a.V + 4) a.s₁ L.length 1 0), μ'⟩ ∧
        (∀ i < 2 * (a.m * a.m), μ' (a.y + 4 * i + 1) =
          arr L.toFinset a.Mo (2 * a.V + 1) i + (6 * a.V + 4)) ∧
        KeptCol μ μ' a.fr a.y (2 * (a.m * a.m)) 1 := by
  have  := h.word_le
  -- sg := 1; g := G; s := s₁; len := l₁; off := 1; δ := 0
  light_set 1
  light_set (6 * a.V + 4)
  light_set a.s₁
  light_set L.length using hl
  light_set (1 : ℕ)
  light_set (0 : ℕ)
  light_piece (place_col hR hT (h.pass hS (Or.inl rfl) (by omega) (Or.inl rfl)
    (by positivity) (by omega)) hS.nodup (pd := 2 * a.V + 1)
    fun i hi => by rw [hpad i hi]; simp [padVal] x)

include hR hT h in
/-- **The pass for the second set.** -/
theorem arrPass₂_ends  (hS : ArrSet μ n a a.s₂ L) (hl : a.l₂ = L.length)
    (hpad : ∀ i < 2 * (a.m * a.m), μ (a.y + 4 * i + 2) = padVal a.V 2) {x}
    {g} {s len off} :
    Ends lim P d (arrPass₂ pResid pTally) ⟨frame (arrLocals a x 1 g s len off 0), μ⟩
      (10 + tPlace L.length a.V) fun σ' =>
      ∃ (x' : ArrScratch) (μ' : Light.Memory),
        σ' = ⟨frame (arrLocals a x' 1 (3 * (6 * a.V + 4)) a.s₂ L.length 2 0), μ'⟩ ∧
        (∀ i < 2 * (a.m * a.m), μ' (a.y + 4 * i + 2) =
          arr L.toFinset a.Mo (2 * a.V + 1) i + 3 * (6 * a.V + 4)) ∧
        KeptCol μ μ' a.fr a.y (2 * (a.m * a.m)) 2 := by
  have  := h.word_le
  light_set (3 * (6 * a.V + 4))
  light_set a.s₂
  light_set L.length using hl
  light_set (2 : ℕ)
  light_piece (place_col hR hT (h.pass hS (Or.inl rfl) (by omega) (Or.inl rfl)
    (by positivity) (by omega)) hS.nodup (pd := 2 * a.V + 1)
    fun i hi => by rw [hpad i hi]; simp [padVal] x)

include hR hT h in
/-- **The pass for the third set.** -/
theorem arrPass₃_ends  (hS : ArrSet μ n a a.s₃ L) (hl : a.l₃ = L.length)
    (hpad : ∀ i < 2 * (a.m * a.m), μ (a.y + 4 * i + 3) = padVal a.V 3) {x}
    {sg g} {s len off δ} :
    Ends lim P d (arrPass₃ pResid pTally) ⟨frame (arrLocals a x sg g s len off δ), μ⟩
      (18 + tPlace L.length a.V) fun σ' =>
      (∀ i < 2 * (a.m * a.m), σ'.mem (a.y + 4 * i + 3) =
        arrZ L.toFinset a.Mo a.V i + 4 * (6 * a.V + 4)) ∧
      KeptCol μ σ'.mem a.fr a.y (2 * (a.m * a.m)) 3 := by
  have  := h.word_le
  light_facts h h.ok
  -- sg := -1; g := 4 G; s := s₃; len := l₃; off := 3; δ := 4 M
  light_set (-1)
  light_set (4 * (6 * a.V + 4))
  light_set a.s₃
  light_set L.length using hl
  light_set (3 : ℕ)
  light_set (4 * a.Mo : ℕ)
  light_piece (place_colZ hR hT (h.pass hS (Or.inr rfl) (by omega) (Or.inr rfl)
    (by positivity) (by omega)) hS.nodup fun i hi => by rw [hpad i hi]; simp [padVal] x)

/-- The four kinds of cells make up the one-array instance of the node. -/
theorem oneArray_of_cells {ν : Node} {V y c} (h₀ : ∀ i < c, μ (y + 4 * i + 0) = padVal V 0)
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
  · aesop
  ram_safe

/-- **The whole routine**, for the arguments a and the three sets as lists. -/
theorem nodeArrayBody_ends {L₁ L₂ L₃} (hR : ResidSpec lim P pResid)
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

end

/-- **nodeArray meets its specification**, in every program that holds its body and meets the
specifications of the two routines that it calls. -/
theorem nodeArray_spec {p pResid pTally} (hp : P[p]? = some (nodeArrayBody pResid pTally))
    (hR : ResidSpec lim P pResid) (hT : TallySpec lim P pTally) : NodeArraySpec lim P p := by
  rintro ⟨⟨fr, n, V, m, np, pr, cnt⟩, ⟨s₁, l₁, S₁⟩, ⟨s₂, l₂, S₂⟩, ⟨s₃, l₃, S₃⟩⟩ Mo y μ
    ⟨henv, h₁, h₂, h₃⟩ hM hMm ⟨hy, ay₁, ay₂, ay₃, ayc⟩ d hok
  obtain ⟨L₁, rfl, seg₁, nodup₁, rfl⟩ : SetAt μ s₁ l₁ S₁ := h₁.set
  obtain ⟨L₂, rfl, seg₂, nodup₂, rfl⟩ : SetAt μ s₂ l₂ S₂ := h₂.set
  obtain ⟨L₃, rfl, seg₃, nodup₃, rfl⟩ : SetAt μ s₃ l₃ S₃ := h₃.set

  dsimp only at hy ay₁ ay₂ ay₃ ayc hM hMm hok ⊢
  rw [(by ring : 8 * m ^ 2 = 4 * (2 * (m * m)))] at hy ay₁ ay₂ ay₃ ayc ⊢
  refine .of_body hp ((nodeArrayBody_ends
    (a := ⟨Mo, s₁, L₁.length, s₂, L₂.length, s₃, L₃.length, V, m, y, cnt, fr⟩) hR hT
    ⟨hM, hMm, henv.zero, henv.belowCnt, hy, ayc, hok⟩
    ⟨seg₁, nodup₁, fun x hx => h₁.bdd x (List.mem_toFinset.2 hx), h₁.le, h₁.below, h₁.apart, ay₁⟩
    ⟨seg₂, nodup₂, fun x hx => h₂.bdd x (List.mem_toFinset.2 hx), h₂.le, h₂.below, h₂.apart, ay₂⟩
    ⟨seg₃, nodup₃, fun x hx => h₃.bdd x (List.mem_toFinset.2 hx), h₃.le, h₃.below, h₃.apart, ay₃⟩
    rfl rfl rfl).mono ?_ fun _ h => h)
  simp only [tNodeArray, tPlace, sq]
  omega

end Light.Sec3.ChanHe
