module
public import GafniTao.WooleyWeightedMean

@[expose] public section

/-!
# Mixed finite means for nested efficient congruencing

This file introduces the literal finite-grid specialization of Wooley
equations (3.19)--(3.20).  In particular, separation is tested on the actual
least nonnegative residue representatives modulo `p^nu`; it is not supplied
as an abstract predicate.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

/-- Wooley's triangular number `R = r(r+1)/2`. -/
def wooleyTriangular (r : ℕ) : ℕ := r * (r + 1) / 2

/-- Two residue classes at possibly different depths are separated modulo
`p^nu`, as in the condition following equation (3.20). -/
def wooleyResiduesSeparated {p a b : ℕ}
    (nu : ℕ) (xi : ZMod (p ^ a)) (eta : ZMod (p ^ b)) : Prop :=
  xi.val % (p ^ nu) ≠ eta.val % (p ^ nu)

instance {p a b nu : ℕ} :
    DecidableRel (wooleyResiduesSeparated (p := p) (a := a) (b := b) nu) :=
  fun xi eta => Classical.propDecidable
    (wooleyResiduesSeparated nu xi eta)

theorem wooleyTriangular_zero : wooleyTriangular 0 = 0 := by
  simp [wooleyTriangular]

theorem wooleyTriangular_one : wooleyTriangular 1 = 1 := by
  norm_num [wooleyTriangular]




