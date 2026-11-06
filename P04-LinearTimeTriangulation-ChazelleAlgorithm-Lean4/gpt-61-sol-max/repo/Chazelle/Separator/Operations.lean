module

public meta import Chazelle.Arithmetic

public import Chazelle.Separator.Maps
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Operations on combinatorial maps (planar separators, part 2)

**Adding an edge inside a face** (`CombMap.addEdge`).  Let `a ≠ b` be two darts of the same face,
`b = fperm^k a` with `k` minimal.  The *arc* `arc a k = {a, fperm a, …, fperm^(k-1) a}` is the
part of the face walk from `a` up to (excluding) `b`.  The new map has darts `D ⊕ Bool`:
the new dart `inr true` is inserted in the rotation just before `a` (at `vert a`), the new dart
`inr false` just before `b` (at `vert b`), and they are opposite to each other.  The face of `a`
splits into the new face `none = arc ∪ {inr false}` and the old face `some (face a)` which keeps
the other darts together with `inr true`; all other faces are unchanged.  Hence
`V' = V`, `E' = E + 1`, `F' = F + 1`, so the Euler characteristic and connectivity are
preserved (`addEdge_planar`).  The face degrees are computed exactly (`addEdge_faceDeg_none`,
`addEdge_faceDeg_some_self`, `addEdge_faceDeg_some_of_ne`).

**Triangulation** (`exists_triangulation`).  Iterating the operation on a face of degree
`≥ 4` with `b = fperm² a` cuts off a triangle; the excess `Σ_g (deg g - 3)` drops by one.  Every
planar map therefore extends (same vertex type, old darts embedded with the same endpoints) to a
planar map all of whose faces have degree `≤ 3`.  Faces of degree `1` and `2` (loops, parallel
edges) are allowed: the separator argument only needs each face to have at most three darts.

Edge deletion (between two distinct faces) and contraction (deletion in the dual) are in
`Delete.lean`; the separator proof itself only adds edges (the Lipton–Tarjan step works on the
triangulation of the whole map, with the BFS levels of the original map, so no contraction of
the levels below `l₀` and no deletion of the levels above `l₂` is needed; see
`LiptonTarjan.lean`).
-/

namespace Chazelle.Separator

universe uF uD

@[expose] public section

open Equiv Finset Sum

namespace CombMap

variable {V F D : Type*} [DecidableEq D] (M : CombMap V F D)

/-! ### The arc of a face between two darts -/



/-! ### The new permutations and labels -/



/-! ### Triangulation -/



end CombMap

end

end Chazelle.Separator
