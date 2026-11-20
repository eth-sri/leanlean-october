/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
module

public import ThreeSumApsp.Util.List

/-!
# One pass over a list

The routines of the reduction after Chan and He ([CH20, Theorem 5.1], one of the reductions behind
Theorem 21(a)) run through arrays from left to right.  This file says what two kinds of
passes have written after the first `i` elements, and how one more element changes it.

* A filter pass selects elements and writes a function of them: `passList`, with one lemma for an
  element that is selected (`passList_succ_of`) and one for an element that is not
  (`passList_succ_of_not`).
* A pass over a sorted list writes the distinct values and their multiplicities.  `DistSt L D i`
  says that `D` is the list of the distinct values among the first `i` elements, and `countTo L i`
  counts occurrences among them.  An element either opens a new value (`DistSt.opens`,
  `map_countTo_opens`) or repeats the last one (`DistSt.bumps`, `map_countTo_bumps`).
-/

@[expose] public section

namespace ThreeSumApsp.Spec

/-! ## A filter pass -/

section Filter

variable {α β : Type}

/-- What a filter pass has written after it has seen the first `i` elements. -/
def passList (p : α → Bool) (f : α → β) (Z : List α) (i : ℕ) : List β := ((Z.take i).filter p).map f

section
variable (p : α → Bool)
  (f : α → β)
  (Z : List α)

/-- At the start nothing is written. -/
@[simp] theorem passList_zero : passList p f Z 0 = [] := by
  rfl

/-- At the end all the selected elements are written. -/
theorem passList_length :
    passList p f Z Z.length = (Z.filter p).map f := by
  simp [passList]

end

section
variable {p : α → Bool}
  (f : α → β)
  {Z : List α}
  {i : ℕ}
  (hi : i < Z.length)
include hi

/-- An element that is selected is written. -/
theorem passList_succ_of
    (h : p Z[i] = true) : passList p f Z (i + 1) = passList p f Z i ++ [f Z[i]] := by
  unfold passList
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.filter_append]
  simp [h]

/-- An element that is not selected changes nothing. -/
theorem passList_succ_of_not
    (h : p Z[i] = false) : passList p f Z (i + 1) = passList p f Z i := by
  unfold passList
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.filter_append]
  simp [h]

end

/-- After `i` elements at most `i` are written. -/
theorem length_passList_le (p : α → Bool) (f : α → β) (Z : List α) (i : ℕ) :
    (passList p f Z i).length ≤ i := by
  rw [passList]
  grind

end Filter

/-! ## The distinct values of a sorted list -/

section
variable (L : List ℤ)
  (i : ℕ)
  (x : ℤ)

end

/-- `D` is the list of the distinct values among the first `i` elements of `L`, and it ends with
the last of them. -/
structure DistSt (L D : List ℤ) (i : ℕ) : Prop where
  nodup : D.Nodup
  mem : ∀ x, x ∈ D ↔ x ∈ L.take i
  le : D.length ≤ i
  last : 0 < i → 0 < D.length ∧ D.getD (D.length - 1) 0 = L.getD (i - 1) 0

section
variable {L D : List ℤ}
  {i : ℕ}
  (h : DistSt L D i)
include h

end

end ThreeSumApsp.Spec
