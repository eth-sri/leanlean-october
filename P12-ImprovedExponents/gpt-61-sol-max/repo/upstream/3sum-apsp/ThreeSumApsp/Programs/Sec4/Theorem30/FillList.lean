/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.Types
public import Mathlib.Tactic
public import ThreeSumApsp.Lang.Tactics
public import ThreeSumApsp.Programs.Sec4.Theorem30.Contracts
public import ThreeSumApsp.Spec.Sec4.Theorem30.PartialSums

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

@[expose] public section

open ThreeSumApsp

namespace Light.Sec4

open ThreeSumApsp.Spec

/-! ## The trie array after the first boxes -/

section

variable {L m t : ℕ} {encA encB : Leaf L → ℤ} {e tile lo : ℕ} {roots : ℕ → ℕ}
  {old : ℕ × List ℕ → Option ℤ} {T : List ℤ}

/-- The trie array after the first i boxes with e stars. -/
def fillAt L m t (encA encB : Leaf L → ℤ) root e T i :=
  fillTrie (arrT encA) (arrT encB) root e ((starBoxes L m t e).take i) T

private theorem fillAt_zero root : fillAt L m t encA encB root e T 0 = T := rfl

private theorem fillAt_length root :
    fillAt L m t encA encB root e T (nineStrs L e (m - t)).length
      = fillTrie (arrT encA) (arrT encB) root e (starBoxes L m t e) T := by
  rw [fillAt, ← length_starBoxes_eq_length_nineStrs, List.take_length]

/-- One more box: it is inserted with the value computed from the array so far. -/
private theorem fillAt_succ root {i} hi :
    fillAt L m t encA encB root e T (i + 1)
      = trieInsert (fillAt L m t encA encB root e T i) root
          (starFirst e (nineStrs L e (m - t))[i])
          (boxValue (arrT encA) (arrT encB) (fillAt L m t encA encB root e T i) root e
            (starFirst e (nineStrs L e (m - t))[i])) := by
  have hi' : i < (starBoxes L m t e).length := by rwa [length_starBoxes_eq_length_nineStrs]

  unfold fillAt fillTrie
  rw [← List.take_append_getElem hi', List.foldl_append, (by simp [starBoxes] : (starBoxes L m t e)[i] = starFirst e (nineStrs L e (m - t))[i])]
  rfl

/-- What the tries hold after the first i boxes. -/
private def fillAt_rep hroot
    (hrep : TrieRep L lo T roots (storedUpTo old tile (arrT encA) (arrT encB) L m t e [])) i :=
  fillTrie_rep hroot ((starBoxes L m t e).take i) [] T (fun _ hl => List.mem_of_mem_take hl) hrep

/-- The array grows by at most 11 L cells for each box. -/
private def length_fillAt_le root i :=
  (length_fillTrie_le (arrT encA) (arrT encB) root e L ((starBoxes L m t e).take i)
    (fun _ hl => (starBoxes_digits (List.mem_of_mem_take hl)).1) T).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (List.length_take_le _ _)) _)

/-- An entry of the array of an encoding is a value of the encoding. -/
private theorem abs_getD_arrT_le (enc : Leaf L → ℤ) {A} (hA : ∀ τ, |enc τ| ≤ A) {c}
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
private theorem exists_starBox {e'} {Ti} {pre} {bx} {A B}
    (hA : ∀ τ, |encA τ| ≤ A) (hB : ∀ τ, |encB τ| ≤ B)
    (hrep : TrieRep L lo Ti roots
      (storedUpTo old tile (arrT encA) (arrT encB) L m t (e' + 1) pre))
    (hbx : bx ∈ starBoxes L m t (e' + 1)) :
    ∃ p, StarBox L encA encB Ti (roots tile) e' bx (10 ^ (e' + 1) * (A * B)) p := by
  obtain ⟨p, hp, hset⟩ := exists_lastStar_of_mem_starBoxes hbx
  obtain ⟨π, rfl⟩ := exists_of_mem_starBoxes bx hbx
  have hpL : p < L := by
    grind [lastStar_eq_some_iff, length_digitsC]
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

end

/-! ## The program -/



/-- The value of a box without stars: the product of the two encoded numbers at its code. -/
def fillValueZero :=
  .call 44 [v 7, v 8] 13 ;;
  .set 12 (M (v 2 +' v 13) *' M (v 3 +' v 13))

/-- The value of the box: for a box with stars, the sum of ten values looked up in the trie that is
being filled. -/
def fillValue : Stmt :=
  .ite (v 0 =' k 0) fillValueZero
    (.call 48 [v 4, v 1, v 7, v 8, v 11] 12)

/-- The end of a round: insert the box with its value, and form the next leaf. -/
def fillTailStmt :=
  .call 46 [v 4, v 1, v 7, v 8, v 12, v 5] 14 ;;
  .call 41 [v 6, v 8, v 0, v 9] 10

/-- One round: the box of the leaf, its value, the insertion, the next leaf. -/
def fillRound :=
  .call 43 [v 6, v 7, v 8, v 0] 11 ;;
  fillValue ;;
  fillTailStmt

/-- fillList(e, root, encA, encB, area, free, leaf, box, len, m - t): start with the least leaf, and
handle one leaf in each round as long as there is another. -/
def fillListBody :=
  .call 40 [v 6, v 8, v 0] 14 ;;
  .set 10 (k 1) ;;
  .while (v 10 =' k 1) fillRound

namespace FillListArgs

variable (x : FillListArgs)

/-- The leaves that the run goes through. -/
abbrev leaves := nineStrs x.L x.e (x.m - x.t)

/-- The trie array after the first i boxes. -/
abbrev trieAt i := fillAt x.L x.m x.t x.encA x.encB x.root x.e x.T i

/-- The value that the routine computes for a box, from the trie array Ti. -/
abbrev value Ti bx :=
  boxValue (arrT x.encA) (arrT x.encB) Ti x.root x.e bx

/-- The locals: the ten arguments, and then More, LastStar, Value, Code and Junk. -/
abbrev locals more star value code junk :=
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

section

variable {lim : Limits} {P : Program} {d : ℕ} {μ : Light.Memory} {x : FillListArgs} {i : ℕ} {l : List ℕ}
  {Ti : List ℤ} {ν : Light.Memory} {more star value code junk : ℤ}

end

end FillList

end Light.Sec4
