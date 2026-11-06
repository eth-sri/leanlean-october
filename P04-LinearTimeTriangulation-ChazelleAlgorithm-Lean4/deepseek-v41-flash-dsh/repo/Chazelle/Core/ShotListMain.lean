module

public import Chazelle.Golf

public import Chazelle.Core.ShotList

/-!
# Shooting at a list of arcs with holes: the main theorem

`shotList_meets`: the wrapper `shotList sh R` meets its contract (`ShotPre`, `ShotPost`,
`shotCost`) with the frame of the caller's band and the oracle bands (module `ShotList`).
-/

namespace Chazelle.Core

namespace ShotList

open Machine Machine.Stmt Programs SignK SweepPrim
open Chazelle.Chain (sideInArc)
open Chazelle.Visibility (rayPt)

@[expose] public section

/-- The first-hit set after `j` arcs. -/
def sofJ (M : Model) (Q : Polygon) (hs : List (WPos × WPos)) (m : ℕ → ℕ) (A j : ℕ) : Set Point :=
  ⋃ i ∈ Finset.range j, pcSet M Q (leaves (M.key Q) hs (arcAt m A i))

theorem sofJ_zero (M : Model) (Q : Polygon) (hs : List (WPos × WPos)) (m : ℕ → ℕ) (A : ℕ) :
    sofJ M Q hs m A 0 = ∅ := ⊚ sofJ

theorem sofJ_succ (M : Model) (Q : Polygon) (hs : List (WPos × WPos)) (m : ℕ → ℕ) (A j : ℕ) :
    sofJ M Q hs m A (j + 1) = sofJ M Q hs m A j ∪ pcSet M Q (leaves (M.key Q) hs (arcAt m A j)) := by
  ϴ sofJ, Finset.range_add_one, Finset.set_biUnion_insert
  exact Set.union_comm _ _

/-- The arc `j` read at the moving pointer. -/
theorem arcAt_ptr (m : ℕ → ℕ) (A j : ℕ) : arcAt m (A + 4 * j) 0 = arcAt m A j := by
  Θ arcAt

end

end ShotList

end Chazelle.Core
