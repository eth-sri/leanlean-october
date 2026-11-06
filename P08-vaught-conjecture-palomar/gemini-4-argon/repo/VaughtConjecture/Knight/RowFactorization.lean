/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Semantics
public import VaughtConjecture.Knight.Repair

/-! # Whole-lower-row factorization through an owned witness gives mixed-grade locality

Consistency of a designed row at a higher-grade cell `x` asks, at every lower controller `y`, for
a transformation of the row of `y` onto the row of `x` capped at `E_x(y)`.  Rather than a list of
mixed-grade equations, the invariant proposed in simplify.md §8 is **factorization of the entire
lower row through an owned lower witness**: `x` designates, at each lower grade `j`, a witness
`w` of grade `j` over its whole scope and a monotone **decoder** `Dec` with

    E_x(z) = Dec (E_w(z))       for every cell `z` of grade at most `j`.               (13)

If the same-grade rows of `w` and `y` agree below their meet value `a = E_w(y)`,

    min (E_w(z), a) = min (E_y(z), a)       for every `z` below `y`,                  (14)

then, since `E_x(y) = Dec a` and `Dec` is monotone (so preserves minima),

    min (E_x(z), E_x(y)) = Dec (min (E_w(z), a)) = Dec (min (E_y(z), a))
                         = min (Dec (E_y(z)), Dec a),                                  (15)

which **is** the locality witness at `y`: shifter `Dec`, step suppressor with cap `Dec a` up to
grade `j` (`⊥` above), self-visible because `Dec a = E_x(y)` is a label of a grade-`j` cell of
an orderly row.  `locality_of_factorization` proves this; `consistent_of_factorization` packages
it: a row whose every lower controller is served by some owned witness and decoder in this way
respects the semantics on its lower set — the consistency half of arbitrary-depth assembly under
the stated representation invariants.  Cap closure, availability toward full scope, and
bountifulness are not addressed.

The decoder hypotheses are exactly the clauses of a Def. 2.3.9 shifter under the cap: `Dec ⊥ =
⊥`, monotone, with `⊥` outputs stable under visibility replacement of the input (so that the
suppressor's `⊥` above grade `j` is compatible with clause 5; the counted decoder of
`Knight/CountedRecoding.lean` sends its whole zero block to `⊥`, so it does not reflect `⊥`),
and commuting with visibility replacement at thresholds `≤ j` under the cap.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-! ## Step suppressors and decoders -/

/-- A **decoder** at grade `j` under the cap `c`: a shifter fixing `⊥`, monotone, reflecting `⊥`,
and commuting with visibility replacement at thresholds `≤ j` under the cap. -/
structure Decoder (j : ℕ) (c : ExtOrd) where
  /-- The decoding map. -/
  toFun : ExtOrd → ExtOrd
  /-- It fixes `⊥`. -/
  bot : toFun ⊥ = ⊥
  /-- It is monotone. -/
  mono : Monotone toFun
  /-- `⊥` outputs are stable under visibility replacement of the input. -/
  bot_evr : ∀ (a : ExtOrd) (k i : ℕ), toFun a = ⊥ → toFun (extVisibilityReplace a k i) = ⊥
  /-- Clause 5 under the cap, at thresholds `≤ j`. -/
  comm : ∀ (a : ExtOrd) (k : ℕ), k ≤ j → toFun a ≤ c → ∀ i ≤ k,
    toFun (extVisibilityReplace a k i) = extVisibilityReplace (toFun a) k i

/-! ## Factorization data at one lower controller -/

/-- The cell `z` below `x` of grade `≤ j` as a cell below the full-scope witness at grade `j`. -/
def toWitness {x : Cell D} {w : D.below (D.cell x)} {j : ℕ}
    (hw : D.cell w.1 = ((D.cell x).1, j)) (z : D.below (D.cell x)) (hz : D.grade z.1 ≤ j) :
    D.below (D.cell w.1) :=
  ⟨z.1, by rw [hw]; exact ⟨z.2.1, hz⟩⟩

@[simp] theorem toWitness_val {x : Cell D} {w : D.below (D.cell x)} {j : ℕ}
    (hw : D.cell w.1 = ((D.cell x).1, j)) (z : D.below (D.cell x)) (hz : D.grade z.1 ≤ j) :
    (toWitness hw z hz).1 = z.1 := rfl

/-- **Factorization of the row of `x` at the controller `y`** through the owned witness `w` at
grade `j` with decoder `Dec`: (13) on every cell of grade `≤ j`, and (14) below `y`. -/
structure Factorization (sem : Semantics D) (x : Cell D) (y : D.below (D.cell x)) where
  /-- The lower grade. -/
  j : ℕ
  /-- `y` has grade `j`. -/
  grade_y : D.grade y.1 = j
  /-- The owned witness. -/
  w : D.below (D.cell x)
  /-- … over the whole scope of `x`, at grade `j`. -/
  cell_w : D.cell w.1 = ((D.cell x).1, j)
  /-- The decoder, capped at `E_x(y)`. -/
  Dec : Decoder j (sem.E x y)
  /-- **(13)**: the row of `x` factors through the row of `w` on cells of grade `≤ j`. -/
  factor : ∀ (z : D.below (D.cell x)) (hz : D.grade z.1 ≤ j),
    sem.E x z = Dec.toFun (sem.E w.1 (toWitness cell_w z hz))
  /-- **(14)**: the rows of `w` and `y` agree below the meet value `a = E_w(y)`. -/
  meet : ∀ z : D.below (D.cell y.1),
    min (sem.E w.1 (toWitness cell_w (below.incl y z) (by
      rw [show D.grade (below.incl y z).1 = D.grade z.1 from rfl]
      exact (z.2.2 : D.grade z.1 ≤ D.grade y.1).trans grade_y.le)))
      (sem.E w.1 (toWitness cell_w y grade_y.le)) =
    min (sem.E y.1 z) (sem.E w.1 (toWitness cell_w y grade_y.le))

variable {sem : Semantics D} {x : Cell D} {y : D.below (D.cell x)}

/-! ## Consistency of a factored row -/

end VaughtConjecture.Knight
