/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import ThreeSumApsp.Slots
import ThreeSumApsp.Lang.Tactics
import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts
import ThreeSumApsp.Spec.Sec4.Theorem30.PartialSums

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

variable (root : ℕ)


theorem fillAt_length :
    fillAt L m t encA encB root e T (nineStrs L e (m - t)).length
      = fillTrie (arrT encA) (arrT encB) root e (starBoxes L m t e) T := by
  grind [fillAt, length_starBoxes_eq_length_nineStrs, List.take_length]

/-- One more box: it is inserted with the value computed from the array so far. -/
theorem fillAt_succ {i : ℕ} (hi : i < (nineStrs L e (m - t)).length) :
    fillAt L m t encA encB root e T (i + 1)
      = trieInsert (fillAt L m t encA encB root e T i) root
          (starFirst e (nineStrs L e (m - t))[i])
          (boxValue (arrT encA) (arrT encB) (fillAt L m t encA encB root e T i) root e
            (starFirst e (nineStrs L e (m - t))[i])) := by
  grind [starBoxes, length_starBoxes_eq_length_nineStrs, starFirst, nineStrs, fillAt, fillTrie, List.take_append_getElem]

/-- What the tries hold after the first i boxes. -/
theorem fillAt_rep (hroot : roots tile ≠ 0)
    (hrep : TrieRep L lo T roots (storedUpTo old tile (arrT encA) (arrT encB) L m t e [])) (i : ℕ) :
    TrieRep L lo (fillAt L m t encA encB (roots tile) e T i) roots
      (storedUpTo old tile (arrT encA) (arrT encB) L m t e ((starBoxes L m t e).take i)) :=
  fillTrie_rep hroot _ [] T (by grind) hrep

/-- The array grows by at most 11 L cells for each box. -/
theorem length_fillAt_le (i : ℕ) :
    (fillAt L m t encA encB root e T i).length ≤ T.length + 11 * L * i :=
  (length_fillTrie_le _ _ root e L _
    (by grind [starBoxes_digits, List.mem_of_mem_take]) T).trans
    (by bound)

variable {A : ℤ}

/-- An entry of the array of an encoding is a value of the encoding. -/
theorem abs_getD_arrT_le (enc : Leaf L → ℤ) (hA : ∀ τ, |enc τ| ≤ A) {c : ℕ}
    (hc : c < 10 ^ L) : |(arrT enc).getD c 0| ≤ A := by
  grind [arrT, decodeT, getD_arrStr_of_lt, termEquiv]

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
theorem exists_starBox {e' : ℕ} {Ti : List ℤ} {pre : List (List ℕ)} {bx : List ℕ} {B : ℤ}
    (hA : ∀ τ, |encA τ| ≤ A) (hB : ∀ τ, |encB τ| ≤ B)
    (hrep : TrieRep L lo Ti roots
      (storedUpTo old tile (arrT encA) (arrT encB) L m t (e' + 1) pre))
    (hbx : bx ∈ starBoxes L m t (e' + 1)) :
    ∃ p, StarBox L encA encB Ti (roots tile) e' bx (10 ^ (e' + 1) * (A * B)) p := by
  obtain ⟨p, hp, hset⟩ := exists_lastStar_of_mem_starBoxes hbx
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes bx hbx
  have hpL : p < L := by
    grind [lastStar_eq_some_iff, List.getD_eq_default, length_digitsC]
  have hstored : ∀ d < 10, storedUpTo old tile _ _ L m t _ pre
      (tile, (digitsC π).set p d)
        = some (dpValueD (arrT encA) (arrT encB) e' ((digitsC π).set p d)) := fun d hd =>
    storedUpTo_of_lt pre (Nat.lt_succ_self e') (by simp_all)
  have hmap : tenValues _ _ p
      = tenValues (dpValueD (arrT encA) (arrT encB) e') (digitsC π) p :=
    List.map_congr_left fun d hd => hrep.lookup tile _
      (starBoxes_digits).2 _ (by simp_all)
  refine ⟨p, hp, hpL, fun d hd => hrep.walkOK tile _ (starBoxes_digits).2 _
    (by aesop), fun j => ?_, by grind [boxValue, sumAtLastStar]⟩
  rw [hmap]
  exact abs_dp_partial_sum_le hA hB e' π ⟨p, hpL⟩ j

end pure

/-! ## The program -/

namespace FillList

/- The local variables of fillList: the arguments (the number e of stars, the root of the trie of
the tile, the addresses of the two encodings, the base of the trie area, the address of the free
pointer, the addresses of the leaf and of the box, their length, and m - t), whether there is
another leaf, the position of the last star, the value of the box, its code, and results that are
not used. -/
slots Stars Root EncA EncB Area Free LeafAt BoxAt Len MaxNines More LastStar Value Code Junk

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

