module

public import Mathlib.Tactic
public import ThreeSumApsp.Util.Types
public import ThreeSumApsp.Util.RamArith
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.FillList
public import ImprovedExponents.PrunedProgram.Tiles.Contracts
import all ThreeSumApsp.Programs.Sec4.Theorem30.FillList

@[expose] public section

/-!
# The boxes with e stars go into the trie of their tile, on pruned encodings

Upstream's `fillList_spec` proves `fillListBody` (procedure 49) under `FillListPre`, with the two
encodings of the tile as full arrays.  The routine reads an encoding cell in one place only: the
value of a box without stars is the product of the two encoded numbers at its code
(`fillValueZero`), and the code is that of a string of `nineStrs L 0 (m - t)`, whose leaf has
at most `m - t ≤ m` symbols `P₀` (`mem_nineStrs`, `card_P0Levels`).  So the same body meets the
same specification when the encodings are right at these leaves only (`FillListPreP`,
`fillListP_meets`).  The proof is upstream's with `SegOn` in place of `Seg` in the invariant of
the loop (`MemInvP`, `RoundFactsP`) and the bridge `SegOn.get_ofDigitList` in
`value_zero_spec`; the lemmas about lists (`fillAt`, `StarBox`) are reused.

Adapted from upstream `ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean` (Apache-2.0).
-/

namespace Light.Sec4

open ThreeSumApsp ThreeSumApsp.Spec

open private fillAt_zero fillAt_length fillAt_succ fillAt_rep length_fillAt_le abs_getD_arrT_le
  exists_starBox from ThreeSumApsp.Programs.Sec4.Theorem30.FillList

/-! ## The bridge: the cell of the code of a string with few nines -/

/-- The cell of the code of a string of `L` digits with at most `m` nines holds the entry of the
array of the encoding: the string is the list of digits of a leaf with as many symbols `P₀` as it
has nines. -/
theorem SegOn.get_ofDigitList {L m} {μ} {a} {enc : Leaf L → ℤ}
    (h : SegOn m μ a enc) {l} (hl : l.length = L) (hd : ∀ d ∈ l, d < 10)
    (hc : l.count 9 ≤ m) :
    μ (a + ofDigitList 10 l) = (arrT enc).getD (ofDigitList 10 l) 0 := by
  obtain ⟨τ, rfl⟩ := exists_digitsT l hl hd
  rw [ofDigitList_digitsT, getD_arrT]
  exact h.get (by rwa [card_P0Levels])

/-- A string of `nineStrs L e (m - t)` has at most `m` nines. -/
def count_nine_le_of_mem_nineStrs {L m t e} {l} (hl : l ∈ nineStrs L e (m - t)) :=
  ((mem_nineStrs l).1 hl).2.2.2.trans (Nat.sub_le m t)

/-! ## The program -/



namespace FillList

/-- The memory ν before round number i: leaf number i, if there is one, is at cur; the first i
boxes have been inserted; the two encodings are right at the leaves with few symbols `P₀`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.MemInv)
structure MemInvP (μ : Light.Memory) (x : FillListArgs) (i : ℕ) (ν : Light.Memory) : Prop where
  leaf : ∀ h , SegN ν x.cur x.leaves[i]
  trie : TrieMem ν x.tr x.cap x.fp (x.trieAt i)
  segA : SegOn x.m ν x.aA x.encA
  segB : SegOn x.m ν x.aB x.encB
  same : SameOutsideTile μ ν x.L x.tr x.cap x.fp x.cur x.box

/-- The invariant of the loop, before round number i: the arguments are in place, More says
whether there is a leaf number i, and the memory is as `MemInvP` says. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.Inv)
def InvP μ x i (σ : State) :=
  ∃ (star value code junk : ℤ) (ν : Light.Memory),
    σ = ⟨x.locals (if i < x.leaves.length then 1 else 0) star value code junk, ν⟩ ∧
      MemInvP μ x i ν

/-- What is known in round number i once the box has been written: l is the leaf, Ti the trie
array before the round, ν the memory. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.RoundFacts)
structure RoundFactsP (μ : Light.Memory) (x : FillListArgs) (i : ℕ) (l : List ℕ) (Ti : List ℤ)
    (ν : Light.Memory) : Prop where
  leaf_mem : l ∈ x.leaves
  box_mem : starFirst x.e l ∈ starBoxes x.L x.m x.t x.e
  /-- nineNext goes to leaf number i + 1. -/
  next : nineNext x.e (x.m - x.t) l = x.leaves[i + 1]?
  /-- The round inserts the box with its value. -/
  succ : x.trieAt (i + 1) = trieInsert Ti x.root (starFirst x.e l) (x.value Ti (starFirst x.e l))
  /-- The trie holds the boxes with fewer stars and the first i boxes with e stars. -/
  rep : TrieRep x.L x.lo Ti x.roots (x.stored ((starBoxes x.L x.m x.t x.e).take i))
  room : Ti.length + 11 * x.L ≤ x.cap
  trie : TrieMem ν x.tr x.cap x.fp Ti
  segA : SegOn x.m ν x.aA x.encA
  segB : SegOn x.m ν x.aB x.encB
  leaf : SegN ν x.cur l
  box : SegN ν x.box (starFirst x.e l)
  same : SameOutsideTile μ ν x.L x.tr x.cap x.fp x.cur x.box

section

variable {lim : Limits} {P : Program} {d : ℕ} {μ : Light.Memory} {x : FillListArgs} {i : ℕ} {l : List ℕ}
  {Ti : List ℤ} {ν : Light.Memory} {more star value code junk : ℤ}

variable (K : Callees lim P)

variable (H : FillListPreP lim μ x) (hd : d + 2 ≤ lim.depth)

include K H hd in
/-- The end of a round: the box is inserted with its value, and the next leaf is formed. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.tail_spec)
private theorem tail_spec
    (R : RoundFactsP μ x i l Ti ν) :
    Ends lim P d fillTailStmt
      ⟨x.locals more star (x.value Ti (starFirst x.e l)) code junk, ν⟩
      (tInsert x.L + tNineNext x.L + 14) (InvP μ x (i + 1)) := by

  have  := length_of_mem_nineStrs R.leaf_mem
  obtain ⟨hbox_len, hbox_digits⟩ := starBoxes_digits R.box_mem
  have  := H.ctx.layout
  have  := R.same
  have hmore : (if (nineNext x.e (x.m - x.t) l).isSome then (1 : ℤ) else 0)
      = if i + 1 < x.leaves.length then 1 else 0 := by
    rw [R.next]
    simp
  -- junk := insert(area, root, box, len, value, free)
  light_call (K.insert
    { tr := x.tr, root := x.root, key := x.box, L := x.L, val := x.value Ti (starFirst x.e l),
      fp := x.fp, cap := x.cap, T := Ti, kl := starFirst x.e l } ν
    { trie := R.trie, seg := R.box, len := hbox_len, digits := hbox_digits
      walk := R.rep.insertOK x.tile H.root_ne _ hbox_len hbox_digits
      room := hbox_len ▸ R.room } _ (by omega)) with _ νins ⟨htrie, hins⟩
  dsimp only at htrie hins
  -- more := nineNext(leaf, len, stars, m - t)
  light_call (K.next x.cur x.L x.e (x.m - x.t) l νins R.leaf.keep R.leaf_mem (by omega) _
    (by omega)) with res νnext ⟨hnextLeaf, hres, hnext⟩
  rw [hmore] at hres
  rw [R.next] at hnextLeaf
  refine ⟨_, _, _, _, νnext, by rw [hres]; rfl, fun h => ?_, ?_, R.segA.keep, R.segB.keep,
    by light_keep⟩
  · simp_all
  · rw [R.succ]
    exact htrie.keep

include K H hd in
/-- The value of a box without stars: the two cells read are those of the code of a string with
at most `m - t ≤ m` nines, which the pruned encodings hold. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean
-- (FillList.value_zero_spec)
private theorem value_zero_spec  (he : x.e = 0) (R : RoundFactsP μ x i l Ti ν) :
    Ends lim P d fillValueZero ⟨x.locals more star value code junk, ν⟩ (tHorner x.L + 14)
      fun σ' => ∃ code' : ℤ,
        σ' = ⟨x.locals more star (x.value Ti (starFirst x.e l)) code' junk, ν⟩ := by
  have C := H.ctx
  have  := C.std.space_le
  have  := C.layout
  have hlen := length_of_mem_nineStrs R.leaf_mem
  have hdigits := ((mem_nineStrs l).1 R.leaf_mem).2.1
  have hnines := count_nine_le_of_mem_nineStrs R.leaf_mem
  obtain ⟨A, B, hA, hB, hword⟩ := C.value_le
  have hbox := R.box
  have hvalue : x.value Ti (starFirst x.e l)
      = (arrT x.encA).getD (ofDigitList 10 l) 0 * (arrT x.encB).getD (ofDigitList 10 l) 0 := by
    rw [FillListArgs.value, he, starFirst_zero, boxValue_zero _ _ Ti x.root hdigits, leafProduct]
  rw [he, starFirst_zero] at hbox
  rw [hvalue]
  have hcode := hlen ▸ ofDigitList_lt l hdigits
  -- the cells of the code hold the encoded numbers: the leaf has at most m symbols P₀
  have hcellA := SegOn.get_ofDigitList R.segA hlen hdigits hnines
  have hcellB := SegOn.get_ofDigitList R.segB hlen hdigits hnines
  -- code := horner(box, len)
  light_call (K.horner x.box x.L l ν hbox hlen hdigits (by omega) C.pow_le _
    (by omega)) with _ ν' ⟨rfl, hν'⟩
  obtain rfl : ν = ν' := hν'.symm
  generalize ofDigitList 10 l = c at hcode hcellA hcellB
  -- the product of two encoded numbers fits in a word
  have hprod : |(arrT x.encA).getD c 0 * (arrT x.encB).getD c 0| ≤ lim.word := by
    have hAc := abs_getD_arrT_le x.encA hA hcode
    rw [abs_mul]
    calc |(arrT x.encA).getD c 0| * |(arrT x.encB).getD c 0|
        ≤ A * B := mul_le_mul hAc (abs_getD_arrT_le x.encB hB hcode) (abs_nonneg _)
          ((abs_nonneg _).trans hAc)
      _ ≤ 10 ^ x.m * (A * B) := le_mul_of_one_le_left
          (mul_nonneg_of_abs_le hA hB) (one_le_pow₀ (by norm_num))
      _ ≤ lim.word := hword
  generalize (arrT x.encA).getD c 0 = y at hcellA hprod
  generalize (arrT x.encB).getD c 0 = z at hcellB hprod
  -- value := mem[encA + code] * mem[encB + code]
  light_set (y * z) using hcellA, hcellB, abs_le.mp hprod
  exact ⟨c, rfl⟩

include K H hd in
/-- The value of a box with stars. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean
-- (FillList.value_succ_spec)
private theorem value_succ_spec  (he : x.e ≠ 0) (R : RoundFactsP μ x i l Ti ν) :
    Ends lim P d (.call 48 [v 4, v 1, v 7, v 8, v 11] 12)
      ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0) value code junk, ν⟩
      (tSumTen x.L + 7) fun σ' =>
        σ' = ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0)
          (x.value Ti (starFirst x.e l)) code junk, ν⟩ := by
  have C := H.ctx
  obtain ⟨hbox_len, hbox_digits⟩ := starBoxes_digits R.box_mem
  obtain ⟨A, B, hA, hB, hword⟩ := C.value_le
  obtain ⟨e', he'⟩ : ∃ e', x.e = e' + 1 := ⟨x.e - 1, by omega⟩
  have  := H.stars_le
  have hrep := R.rep
  have hbox_mem := R.box_mem
  have hbox := R.box
  generalize starFirst x.e l = bx at hbox_mem hbox hbox_len hbox_digits ⊢
  dsimp only [FillListArgs.stored] at hrep
  rw [he'] at hrep hbox_mem
  obtain ⟨p, hstar⟩ := exists_starBox hA hB hrep hbox_mem
  have  := R.trie.le_cap
  have  := C.layout
  -- the partial sums are at most 10^{e'+1} A B ≤ 10^m A B
  have hbound : (10 : ℤ) ^ (e' + 1) * (A * B) ≤ lim.word :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega))
      (mul_nonneg_of_abs_le hA hB)).trans hword
  have hvalue : x.value Ti bx
      = ((List.range 10).map fun d => trieLookup Ti x.root (bx.set p d)).sum := by
    rw [FillListArgs.value, he']
    exact hstar.value
  rw [hvalue, hstar.last]
  -- value := sumTen(area, root, box, len, lastStar)
  light_call (K.box
    { tr := x.tr, root := x.root, box := x.box, L := x.L, p := p, T := Ti, l := bx } ν
    { area := R.trie.seg, seg := hbox, len := hbox_len, star := hbox_len ▸ hstar.lt
      digits := hbox_digits, walk := hstar.walk
      sums := fun j _ => (hstar.sums j).trans hbound } _ hd) with _ ν' ⟨rfl, hν'⟩
  rw [hν']
  rfl

include K H hd in
/-- The value of the box. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean
-- (FillList.fillValue_spec)
private theorem fillValue_spec  (R : RoundFactsP μ x i l Ti ν) :
    Ends lim P d fillValue
      ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0) value code junk, ν⟩
      (tHorner x.L + tSumTen x.L + 18) fun σ' => ∃ code' : ℤ,
        σ' = ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0)
          (x.value Ti (starFirst x.e l)) code' junk, ν⟩ := by
  have  := H.ctx.std.const_le
  -- if stars = 0
  refine Ends.iteLast (fun hz => ?_) fun hz => ?_
  · light_piece (value_zero_spec K H hd (by simpa using hz) R)
  · exact (value_succ_spec K H hd (by simpa using hz) R).mono (by light_time) fun _ h => ⟨code, h⟩

include K H hd in
/-- One round of the loop handles leaf number i. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.round_spec)
private theorem round_spec  (hi : i < x.leaves.length) (I : MemInvP μ x i ν) :
    Ends lim P d fillRound ⟨x.locals more star value code junk, ν⟩ (tFillRound x.L)
      (InvP μ x (i + 1)) := by


  have  := H.ctx.layout
  have hlen := length_of_mem_nineStrs (List.getElem_mem hi)
  have  := I.same
  unfold tFillRound
  -- lastStar := starFirst(leaf, box, len, stars)
  light_call (K.star x.cur x.box x.L x.e _ ν (I.leaf hi) hlen (by omega) (by omega)
    (by omega) _ (by omega)) with _ νbox ⟨hbox, rfl, hsame⟩
  have R : RoundFactsP μ x i x.leaves[i] (x.trieAt i) νbox :=
    { leaf_mem := List.getElem_mem hi, box_mem := starFirst_mem_starBoxes hi
      next := nineNext_getElem x.L x.e (x.m - x.t) i hi, succ := fillAt_succ x.root hi
      rep := fillAt_rep H.root_ne H.rep i, room := by
        have hlen : (x.trieAt i).length ≤ x.T.length + 11 * x.L * i :=
          length_fillAt_le x.root i
        have hmul : 11 * x.L * (i + 1) ≤ 11 * x.L * x.leaves.length := Nat.mul_le_mul_left _ hi
        have  : x.T.length + 11 * x.L * x.leaves.length ≤ x.cap := by
          ram_safe [length_starBoxes_eq_length_nineStrs]
        rw [Nat.mul_add_one] at hmul
        omega
      trie := I.trie.keep, segA := I.segA.keep, segB := I.segB.keep, leaf := (I.leaf hi).keep
      box := hbox, same := by light_keep }
  -- fillValue
  light_piece (fillValue_spec K H hd R) with _ ⟨code', rfl⟩
  -- fillTailStmt
  light_piece (tail_spec K H hd R)

include K H hd in
/-- The whole run. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.body_spec)
private theorem body_spec  :
    Ends lim P d fillListBody ⟨frame x.vals, μ⟩ (tFillList x.L x.leaves.length) fun σ' =>
        TrieMem σ'.mem x.tr x.cap x.fp (x.trieAt x.leaves.length) ∧
          SameOutsideTile μ σ'.mem x.L x.tr x.cap x.fp x.cur x.box := by
  have C := H.ctx
  have  := C.std.const_le
  have heL : x.e ≤ x.L := by ram_safe
  have hpos := length_nineStrs_pos heL H.stars_le

  have  := C.layout
  unfold tFillList
  -- junk := nineFirst(leaf, len, stars)
  light_call (K.first x.cur x.L x.e μ heL (by omega) _ (by omega)) with res ν ⟨hleaf, hsame⟩
  -- more := 1
  light_set (1 : ℕ)
  -- while more = 1
  refine Ends.whileConst (InvP μ x) x.leaves.length (tFillRound x.L) ?start ?round ?done ?time
  case start =>
    refine ⟨0, 0, 0, res, ν, by rw [ite_eq_left hpos]; rfl, fun _ => getElem_nineStrs hpos ▸ hleaf, ?_,
      H.segA.keep, H.segB.keep, by light_keep⟩
    rw [FillListArgs.trieAt, fillAt_zero]
    exact H.trie.keep
  case round =>
    rintro i _ hi ⟨star, value, code, junk, ν', rfl, I⟩
    exact ⟨by simp; omega, by simp [hi], round_spec K H hd hi I⟩
  case done =>
    rintro _ ⟨star, value, code, junk, ν', rfl, I⟩
    exact ⟨by simp; omega, by simp, I.trie, I.same⟩
  case time =>
    -- the test of the loop and a round are the time of one box

    rw [(by
      simp [tFillStep]
      omega
     : (v 10 =' k 1).cost + 1 + tFillRound x.L = tFillStep x.L)]
    light_time

end

end FillList

/-- **fillList on pruned encodings** inserts the boxes with e stars, with their values, into the
trie of their tile. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (fillList_spec)
theorem fillListP_meets {lim} {P} (hP : P[49]? = some fillListBody)
    (hFirst : NineFirstSpec lim P) (hNext : NineNextSpec lim P) (hStar : StarFirstSpec lim P)
    (hHorner : HornerSpec lim P) (hInsert : InsertSpec lim P) (hBox : SumTenSpec lim P) :
    FillListSpecP lim P := by
  intro x μ pre d hd
  rw [FillListArgs.boxes, length_starBoxes_eq_length_nineStrs, ← fillAt_length]
  exact .of_body hP (FillList.body_spec ⟨hFirst, hNext, hStar, hHorner, hInsert, hBox⟩ pre hd)

end Light.Sec4
