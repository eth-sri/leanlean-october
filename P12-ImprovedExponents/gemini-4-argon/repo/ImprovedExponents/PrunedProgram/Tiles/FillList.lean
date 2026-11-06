module

public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts
public import ThreeSumApsp.Spec.Sec4.Theorem30.PartialSums
public import ImprovedExponents.PrunedProgram.Tiles.Contracts

@[expose] public section

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# The boxes with e stars go into the trie of their tile (Lemma 29)

"Given the two encodings of a tile, we can compute the values of all these boxes, and store them in
the trie for that tile, in O(L) time and space per box."  "We compute the values of the boxes in
increasing order of their number of stars."  This routine handles the boxes with e stars.  It goes
through the leaves with between e and m - t symbols P₀ in lexicographic order.  For each of them it
turns the first e nines into stars, which gives the next box with e stars; computes the value of the
box, for e = 0 as the product of the two encoded numbers at its code and for e ≥ 1 as the sum of the
values of ten boxes with e - 1 stars, looked up in the trie of the tile; and inserts the box with
its value into the trie.

1. The first section is about lists only: `fillAt` is the trie array after the first i boxes, and
   `StarBox` collects what the routine needs to know about a box with stars (`exists_starBox`).
2. `FillListArgs` holds the data of one run, `FillListPre` what the routine assumes, and
   `FillList.Callees` the specifications of the routines that are called.  `FillList.Inv` is the
   invariant of the loop, and `FillList.RoundFacts` what is known in a round once the box has been
   written.  A round is the call of starFirst, the value (`value_zero_spec`, `value_succ_spec`,
   `fillValue_spec`) and the end of the round (`tail_spec`); together they are `round_spec`, and
   `body_spec` is the whole run.  `fillList_spec` is the specification.
-/


open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The trie array after the first boxes -/

section pure

variable {L m t : ℕ} {encA encB : Leaf L → ℤ} {e tile lo : ℕ} {roots : ℕ → ℕ}
  {old : ℕ × List ℕ → Option ℤ} {T : List ℤ}

/-- The trie array after the first i boxes with e stars. -/
def fillAt (L m t : ℕ) (encA encB : Leaf L → ℤ) (root e : ℕ) (T : List ℤ) (i : ℕ) : List ℤ :=
  fillTrie (arrT encA) (arrT encB) root e ((starBoxes L m t e).take i) T

theorem fillAt_zero (root : ℕ) : fillAt L m t encA encB root e T 0 = T := by
  simp [fillAt, fillTrie]

theorem fillAt_length (root : ℕ) :
    fillAt L m t encA encB root e T (nineStrs L e (m - t)).length
      = fillTrie (arrT encA) (arrT encB) root e (starBoxes L m t e) T := by
  rw [fillAt, ← length_starBoxes_eq_length_nineStrs, List.take_length]

/-- One more box: it is inserted with the value computed from the array so far. -/
theorem fillAt_succ (root : ℕ) {i : ℕ} (hi : i < (nineStrs L e (m - t)).length) :
    fillAt L m t encA encB root e T (i + 1)
      = trieInsert (fillAt L m t encA encB root e T i) root
          (starFirst e (nineStrs L e (m - t))[i])
          (boxValue (arrT encA) (arrT encB) (fillAt L m t encA encB root e T i) root e
            (starFirst e (nineStrs L e (m - t))[i])) := by
  have hi' : i < (starBoxes L m t e).length := by rwa [length_starBoxes_eq_length_nineStrs]
  have hbox : (starBoxes L m t e)[i] = starFirst e (nineStrs L e (m - t))[i] := by simp [starBoxes]
  unfold fillAt fillTrie
  rw [← List.take_append_getElem hi', List.foldl_append, hbox]
  rfl

/-- What the tries hold after the first i boxes. -/
theorem fillAt_rep (hroot : roots tile ≠ 0)
    (hrep : TrieRep L lo T roots (storedUpTo old tile (arrT encA) (arrT encB) L m t e [])) (i : ℕ) :
    TrieRep L lo (fillAt L m t encA encB (roots tile) e T i) roots
      (storedUpTo old tile (arrT encA) (arrT encB) L m t e ((starBoxes L m t e).take i)) :=
  fillTrie_rep hroot ((starBoxes L m t e).take i) [] T (fun _ hl => List.mem_of_mem_take hl) hrep

/-- The array grows by at most 11 L cells for each box. -/
theorem length_fillAt_le (root i : ℕ) :
    (fillAt L m t encA encB root e T i).length ≤ T.length + 11 * L * i :=
  (length_fillTrie_le (arrT encA) (arrT encB) root e L ((starBoxes L m t e).take i)
    (fun _ hl => (starBoxes_digits (List.mem_of_mem_take hl)).1) T).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (List.length_take_le _ _)) _)

/-- An entry of the array of an encoding is a value of the encoding. -/
theorem abs_getD_arrT_le (enc : Leaf L → ℤ) {A : ℤ} (hA : ∀ τ, |enc τ| ≤ A) {c : ℕ}
    (hc : c < 10 ^ L) : |(arrT enc).getD c 0| ≤ A := by
  have hval : (arrT enc).getD c 0 = enc (decodeT L c) :=
    getD_arrStr_of_lt termEquiv enc hc
  rw [hval]
  exact hA _

/-- What the routine needs to know about a box with e + 1 stars. -/
structure StarBox (L : ℕ) (encA encB : Leaf L → ℤ) (Ti : List ℤ) (root e : ℕ) (bx : List ℕ)
    (bound : ℤ) (p : ℕ) : Prop where
  /-- p is the position of the last star. -/
  last : lastStar bx = some p
  lt : p < L
  /-- The ten strings are stored in the trie. -/
  walk : ∀ d < 10, WalkOK Ti root (bx.set p d)
  /-- The partial sums of their values are bounded. -/
  sums : ∀ j, |((tenValues (trieLookup Ti root) bx p).take j).sum| ≤ bound
  value : boxValue (arrT encA) (arrT encB) Ti root (e + 1) bx
    = (tenValues (trieLookup Ti root) bx p).sum

/-- A box with e' + 1 stars, in a trie that holds the boxes with at most e' stars, is as `StarBox`
says. -/
theorem exists_starBox {e' : ℕ} {Ti : List ℤ} {pre : List (List ℕ)} {bx : List ℕ} {A B : ℤ}
    (hA : ∀ τ, |encA τ| ≤ A) (hB : ∀ τ, |encB τ| ≤ B)
    (hrep : TrieRep L lo Ti roots
      (storedUpTo old tile (arrT encA) (arrT encB) L m t (e' + 1) pre))
    (hbx : bx ∈ starBoxes L m t (e' + 1)) :
    ∃ p, StarBox L encA encB Ti (roots tile) e' bx (10 ^ (e' + 1) * (A * B)) p := by
  obtain ⟨p, hp, hset⟩ := exists_lastStar_of_mem_starBoxes hbx
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes bx hbx
  have hpL : p < L := by
    have hstar := ((lastStar_eq_some_iff _ _).1 hp).1
    by_contra hc
    rw [List.getD_eq_default _ _ (by rw [length_digitsC]; omega)] at hstar
    omega
  have hstored : ∀ d < 10, storedUpTo old tile (arrT encA) (arrT encB) L m t (e' + 1) pre
      (tile, (digitsC π).set p d)
        = some (dpValueD (arrT encA) (arrT encB) e' ((digitsC π).set p d)) := fun d hd =>
    storedUpTo_of_lt pre (Nat.lt_succ_self e') (hset d hd)
  have hmap : tenValues (trieLookup Ti (roots tile)) (digitsC π) p
      = tenValues (dpValueD (arrT encA) (arrT encB) e') (digitsC π) p :=
    List.map_congr_left fun d hd => hrep.lookup tile _
      (starBoxes_digits (hset d (List.mem_range.1 hd))).2 _ (hstored d (List.mem_range.1 hd))
  refine ⟨p, hp, hpL, fun d hd => hrep.walkOK tile _ (starBoxes_digits (hset d hd)).2 _
    (hstored d hd), fun j => ?_, by rw [boxValue, sumAtLastStar, hp]⟩
  rw [hmap]
  exact abs_dp_partial_sum_le hA hB e' π ⟨p, hpL⟩ j

end pure

/-! ## The program -/

namespace FillList

/-- The local variables of fillList: the arguments (the number e of stars, the root of the trie of
the tile, the addresses of the two encodings, the base of the trie area, the address of the free
pointer, the addresses of the leaf and of the box, their length, and m - t), whether there is
another leaf, the position of the last star, the value of the box, its code, and results that are
not used. -/
abbrev Stars : ℕ := 0
@[inherit_doc Stars] abbrev Root : ℕ := 1
@[inherit_doc Stars] abbrev EncA : ℕ := 2
@[inherit_doc Stars] abbrev EncB : ℕ := 3
@[inherit_doc Stars] abbrev Area : ℕ := 4
@[inherit_doc Stars] abbrev Free : ℕ := 5
@[inherit_doc Stars] abbrev LeafAt : ℕ := 6
@[inherit_doc Stars] abbrev BoxAt : ℕ := 7
@[inherit_doc Stars] abbrev Len : ℕ := 8
@[inherit_doc Stars] abbrev MaxNines : ℕ := 9
@[inherit_doc Stars] abbrev More : ℕ := 10
@[inherit_doc Stars] abbrev LastStar : ℕ := 11
@[inherit_doc Stars] abbrev Value : ℕ := 12
@[inherit_doc Stars] abbrev Code : ℕ := 13
@[inherit_doc Stars] abbrev Junk : ℕ := 14

end FillList

open FillList

/-- The value of a box without stars: the product of the two encoded numbers at its code. -/
def fillValueZero : Stmt :=
  .call Proc.horner [v BoxAt, v Len] Code ;;
  .set Value (M (v EncA +' v Code) *' M (v EncB +' v Code))

/-- The value of the box: for a box with stars, the sum of ten values looked up in the trie that is
being filled. -/
def fillValue : Stmt :=
  .ite (v Stars =' k 0) fillValueZero
    (.call Proc.sumTen [v Area, v Root, v BoxAt, v Len, v LastStar] Value)

/-- The end of a round: insert the box with its value, and form the next leaf. -/
def fillTailStmt : Stmt :=
  .call Proc.insert [v Area, v Root, v BoxAt, v Len, v Value, v Free] Junk ;;
  .call Proc.nineNext [v LeafAt, v Len, v Stars, v MaxNines] More

/-- One round: the box of the leaf, its value, the insertion, the next leaf. -/
def fillRound : Stmt :=
  .call Proc.starFirst [v LeafAt, v BoxAt, v Len, v Stars] LastStar ;;
  fillValue ;;
  fillTailStmt

/-- fillList(e, root, encA, encB, area, free, leaf, box, len, m - t): start with the least leaf, and
handle one leaf in each round as long as there is another. -/
def fillListBody : Stmt :=
  .call Proc.nineFirst [v LeafAt, v Len, v Stars] Junk ;;
  .set More (k 1) ;;
  .while (v More =' k 1) fillRound

namespace FillListArgs

variable (x : FillListArgs)

/-- The leaves that the run goes through. -/
abbrev leaves : List (List ℕ) := nineStrs x.L x.e (x.m - x.t)

/-- The trie array after the first i boxes. -/
abbrev trieAt (i : ℕ) : List ℤ := fillAt x.L x.m x.t x.encA x.encB x.root x.e x.T i

/-- The value that the routine computes for a box, from the trie array Ti. -/
abbrev value (Ti : List ℤ) (bx : List ℕ) : ℤ :=
  boxValue (arrT x.encA) (arrT x.encB) Ti x.root x.e bx

/-- The locals: the ten arguments, and then More, LastStar, Value, Code and Junk. -/
abbrev locals (more star value code junk : ℤ) : ℕ → ℤ :=
  frame [x.e, x.root, x.aA, x.aB, x.tr, x.fp, x.cur, x.box, x.L, (x.m - x.t : ℕ), more, star, value,
    code, junk]

end FillListArgs

namespace FillList

/-- The routines that fillList calls meet their specifications. -/
structure Callees (lim : Limits) (P : Program) : Prop where
  first : NineFirstSpec lim P
  next : NineNextSpec lim P
  star : StarFirstSpec lim P
  horner : HornerSpec lim P
  insert : InsertSpec lim P
  box : SumTenSpec lim P

section round

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : FillListArgs} {i : ℕ} {l : List ℕ}
  {Ti : List ℤ} {ν : ℕ → ℤ} {more star value code junk : ℤ}

end round

end FillList






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



/-! ## The bridge: the cell of the code of a string with few nines -/

/-- The cell of the code of a string of `L` digits with at most `m` nines holds the entry of the
array of the encoding: the string is the list of digits of a leaf with as many symbols `P₀` as it
has nines. -/
theorem SegOn.get_ofDigitList {L m : ℕ} {μ : ℕ → ℤ} {a : ℕ} {enc : Leaf L → ℤ}
    (h : SegOn m μ a enc) {l : List ℕ} (hl : l.length = L) (hd : ∀ d ∈ l, d < 10)
    (hc : l.count 9 ≤ m) :
    μ (a + ofDigitList 10 l) = (arrT enc).getD (ofDigitList 10 l) 0 := by
  obtain ⟨τ, rfl⟩ := exists_digitsT l hl hd
  rw [ofDigitList_digitsT, getD_arrT]
  exact h.get (by rwa [card_P0Levels])

/-- A string of `nineStrs L e (m - t)` has at most `m` nines. -/
theorem count_nine_le_of_mem_nineStrs {L m t e : ℕ} {l : List ℕ} (hl : l ∈ nineStrs L e (m - t)) :
    l.count 9 ≤ m :=
  ((mem_nineStrs l).1 hl).2.2.2.trans (Nat.sub_le m t)

/-! ## The program -/


namespace FillList

/-- The memory ν before round number i: leaf number i, if there is one, is at cur; the first i
boxes have been inserted; the two encodings are right at the leaves with few symbols `P₀`. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.MemInv)
structure MemInvP (μ : ℕ → ℤ) (x : FillListArgs) (i : ℕ) (ν : ℕ → ℤ) : Prop where
  leaf : ∀ h : i < x.leaves.length, SegN ν x.cur x.leaves[i]
  trie : TrieMem ν x.tr x.cap x.fp (x.trieAt i)
  segA : SegOn x.m ν x.aA x.encA
  segB : SegOn x.m ν x.aB x.encB
  same : SameOutsideTile μ ν x.L x.tr x.cap x.fp x.cur x.box

/-- The invariant of the loop, before round number i: the arguments are in place, More says
whether there is a leaf number i, and the memory is as `MemInvP` says. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.Inv)
def InvP (μ : ℕ → ℤ) (x : FillListArgs) (i : ℕ) (σ : State) : Prop :=
  ∃ (star value code junk : ℤ) (ν : ℕ → ℤ),
    σ = ⟨x.locals (if i < x.leaves.length then 1 else 0) star value code junk, ν⟩ ∧
      MemInvP μ x i ν

/-- What is known in round number i once the box has been written: l is the leaf, Ti the trie
array before the round, ν the memory. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.RoundFacts)
structure RoundFactsP (μ : ℕ → ℤ) (x : FillListArgs) (i : ℕ) (l : List ℕ) (Ti : List ℤ)
    (ν : ℕ → ℤ) : Prop where
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

section round

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {x : FillListArgs} {i : ℕ} {l : List ℕ}
  {Ti : List ℤ} {ν : ℕ → ℤ} {more star value code junk : ℤ}

/-- The end of a round: the box is inserted with its value, and the next leaf is formed. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.tail_spec)
theorem tail_spec (K : Callees lim P) (H : FillListPreP lim μ x) (hd : d + 2 ≤ lim.depth)
    (R : RoundFactsP μ x i l Ti ν) :
    Ends lim P d fillTailStmt
      ⟨x.locals more star (x.value Ti (starFirst x.e l)) code junk, ν⟩
      (tInsert x.L + tNineNext x.L + 14) (InvP μ x (i + 1)) := by
  have C := H.ctx
  have := length_of_mem_nineStrs R.leaf_mem
  obtain ⟨hbox_len, hbox_digits⟩ := starBoxes_digits R.box_mem
  have := C.layout
  have := R.same
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
  · rwa [List.getElem?_eq_getElem h] at hnextLeaf
  · rw [R.succ]
    exact htrie.keep

/-- The value of a box without stars: the two cells read are those of the code of a string with
at most `m - t ≤ m` nines, which the pruned encodings hold. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean
-- (FillList.value_zero_spec)
theorem value_zero_spec (K : Callees lim P) (H : FillListPreP lim μ x)
    (hd : d + 2 ≤ lim.depth) (he : x.e = 0) (R : RoundFactsP μ x i l Ti ν) :
    Ends lim P d fillValueZero ⟨x.locals more star value code junk, ν⟩ (tHorner x.L + 14)
      fun σ' => ∃ code' : ℤ,
        σ' = ⟨x.locals more star (x.value Ti (starFirst x.e l)) code' junk, ν⟩ := by
  have C := H.ctx
  have := C.std.space_le
  have := C.layout
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
  have hcode : ofDigitList 10 l < 10 ^ x.L := hlen ▸ ofDigitList_lt l hdigits
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

/-- The value of a box with stars. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean
-- (FillList.value_succ_spec)
theorem value_succ_spec (K : Callees lim P) (H : FillListPreP lim μ x)
    (hd : d + 2 ≤ lim.depth) (he : x.e ≠ 0) (R : RoundFactsP μ x i l Ti ν) :
    Ends lim P d (.call Proc.sumTen [v Area, v Root, v BoxAt, v Len, v LastStar] Value)
      ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0 : ℕ) value code junk, ν⟩
      (tSumTen x.L + 7) fun σ' =>
        σ' = ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0 : ℕ)
          (x.value Ti (starFirst x.e l)) code junk, ν⟩ := by
  have C := H.ctx
  obtain ⟨hbox_len, hbox_digits⟩ := starBoxes_digits R.box_mem
  obtain ⟨A, B, hA, hB, hword⟩ := C.value_le
  obtain ⟨e', he'⟩ : ∃ e', x.e = e' + 1 := ⟨x.e - 1, by omega⟩
  have := H.stars_le
  have hrep := R.rep
  have hbox_mem := R.box_mem
  have hbox := R.box
  generalize starFirst x.e l = bx at hbox_mem hbox hbox_len hbox_digits ⊢
  dsimp only [FillListArgs.stored] at hrep
  rw [he'] at hrep hbox_mem
  obtain ⟨p, hstar⟩ := exists_starBox hA hB hrep hbox_mem
  have := R.trie.le_cap
  have := C.layout
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
      sums := fun j _ => (hstar.sums j).trans hbound } _ (by omega)) with _ ν' ⟨rfl, hν'⟩
  rw [hν']
  rfl

/-- The value of the box. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean
-- (FillList.fillValue_spec)
theorem fillValue_spec (K : Callees lim P) (H : FillListPreP lim μ x)
    (hd : d + 2 ≤ lim.depth) (R : RoundFactsP μ x i l Ti ν) :
    Ends lim P d fillValue
      ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0 : ℕ) value code junk, ν⟩
      (tHorner x.L + tSumTen x.L + 18) fun σ' => ∃ code' : ℤ,
        σ' = ⟨x.locals more ((lastStar (starFirst x.e l)).getD 0 : ℕ)
          (x.value Ti (starFirst x.e l)) code' junk, ν⟩ := by
  have := H.ctx.std.const_le
  -- if stars = 0
  refine Ends.iteLast (fun hz => ?_) (fun hz => ?_)
  · light_piece (value_zero_spec K H hd (by simpa using hz) R)
  · exact (value_succ_spec K H hd (by simpa using hz) R).mono (by light_time) fun _ h => ⟨code, h⟩

/-- One round of the loop handles leaf number i. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.round_spec)
theorem round_spec (K : Callees lim P) (H : FillListPreP lim μ x)
    (hd : d + 2 ≤ lim.depth) (hi : i < x.leaves.length) (I : MemInvP μ x i ν) :
    Ends lim P d fillRound ⟨x.locals more star value code junk, ν⟩ (tFillRound x.L)
      (InvP μ x (i + 1)) := by
  have C := H.ctx
  have hroom : (x.trieAt i).length + 11 * x.L ≤ x.cap := by
    have hlen : (x.trieAt i).length ≤ x.T.length + 11 * x.L * i :=
      length_fillAt_le x.root i
    have hmul : 11 * x.L * (i + 1) ≤ 11 * x.L * x.leaves.length := Nat.mul_le_mul_left _ hi
    have : x.T.length + 11 * x.L * x.leaves.length ≤ x.cap := by
      have hroom := H.room
      rwa [FillListArgs.boxes, length_starBoxes_eq_length_nineStrs] at hroom
    rw [Nat.mul_add_one] at hmul
    omega
  have := C.layout
  have hlen := length_of_mem_nineStrs (List.getElem_mem hi)
  have := I.same
  unfold tFillRound
  -- lastStar := starFirst(leaf, box, len, stars)
  light_call (K.star x.cur x.box x.L x.e _ ν (I.leaf hi) hlen (by omega) (by omega)
    (by omega) _ (by omega)) with _ νbox ⟨hbox, rfl, hsame⟩
  have R : RoundFactsP μ x i x.leaves[i] (x.trieAt i) νbox :=
    { leaf_mem := List.getElem_mem hi, box_mem := starFirst_mem_starBoxes hi
      next := nineNext_getElem x.L x.e (x.m - x.t) i hi, succ := fillAt_succ x.root hi
      rep := fillAt_rep H.root_ne H.rep i, room := hroom
      trie := I.trie.keep, segA := I.segA.keep, segB := I.segB.keep, leaf := (I.leaf hi).keep
      box := hbox, same := by light_keep }
  -- fillValue
  light_piece (fillValue_spec K H hd R) with _ ⟨code', rfl⟩
  -- fillTailStmt
  light_piece (tail_spec K H hd R)

/-- The whole run. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (FillList.body_spec)
theorem body_spec (K : Callees lim P) (H : FillListPreP lim μ x)
    (hd : d + 2 ≤ lim.depth) :
    Ends lim P d fillListBody ⟨frame x.vals, μ⟩ (tFillList x.L x.leaves.length) fun σ' =>
        TrieMem σ'.mem x.tr x.cap x.fp (x.trieAt x.leaves.length) ∧
          SameOutsideTile μ σ'.mem x.L x.tr x.cap x.fp x.cur x.box := by
  have C := H.ctx
  have := C.std.const_le
  have heL : x.e ≤ x.L := by have := C.ht; have := C.hmL; have := H.stars_le; omega
  have hpos := length_nineStrs_pos heL H.stars_le
  have hfirst : (nineStrs x.L x.e (x.m - x.t))[0] = nineFirst x.L x.e := getElem_nineStrs hpos
  have := C.layout
  unfold tFillList
  -- junk := nineFirst(leaf, len, stars)
  light_call (K.first x.cur x.L x.e μ heL (by omega) _ (by omega)) with res ν ⟨hleaf, hsame⟩
  -- more := 1
  light_set (1 : ℕ)
  -- while more = 1
  refine Ends.whileConst (InvP μ x) x.leaves.length (tFillRound x.L) ?start ?round ?done ?time
  case start =>
    refine ⟨0, 0, 0, res, ν, by rw [ite_eq_left hpos]; rfl, fun _ => hfirst ▸ hleaf, ?_,
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
    have hstep : (v More =' k 1).cost + 1 + tFillRound x.L = tFillStep x.L := by
      simp [tFillStep]
      omega
    rw [hstep]
    light_time

end round

end FillList

/-- **fillList on pruned encodings** inserts the boxes with e stars, with their values, into the
trie of their tile. -/
-- adapted from upstream ThreeSumApsp/Programs/Sec4/Theorem30/FillList.lean (fillList_spec)
theorem fillListP_meets {lim : Limits} {P : Program} (hP : P[Proc.fillList]? = some fillListBody)
    (hFirst : NineFirstSpec lim P) (hNext : NineNextSpec lim P) (hStar : StarFirstSpec lim P)
    (hHorner : HornerSpec lim P) (hInsert : InsertSpec lim P) (hBox : SumTenSpec lim P) :
    FillListSpecP lim P := by
  intro x μ pre d hd
  rw [FillListArgs.boxes, length_starBoxes_eq_length_nineStrs, ← fillAt_length]
  exact .of_body hP (FillList.body_spec ⟨hFirst, hNext, hStar, hHorner, hInsert, hBox⟩ pre hd)

end Light.Sec4

