module

public import ADR11.Computation.Toolkit

/-!
# Rooted gene tree probabilities in the 5-taxon caterpillar species tree

The two worked examples of Section 3 of the paper, for the caterpillar species tree
`((((a,b):x,c):y,d):z,e)` (`caterpillar5`), with `X = e^{-x}`, `Y = e^{-y}`, `Z = e^{-z}`:

* `rootedDist_cat5_example1`: `ℙ(((((B,E),A),C),D)) = X Y³ Z⁶ / 180`;
* `rootedDist_cat5_example2`: `ℙ((((B,E),A),(C,D))) = X Y³ Z³ / 54 - X Y³ Z⁶ / 540`.

`cat5Shape` is the tree shape of `caterpillar5` for the engine of `ADR11.Computation.Toolkit`.
-/

@[expose] public section

namespace ADR11.Computation

open Finset Real

/-- The tree shape of the caterpillar `((((a,b),c),d),e)` on `Fin 5`. -/
def cat5Shape : PTree :=
  .node 31 [.node 15 [.node 7 [.node 3 [.leaf 0, .leaf 1], .leaf 2], .leaf 3], .leaf 4]

theorem cat5Shape_wfB : cat5Shape.wfB 5 caterpillar5 = true := by decide

end ADR11.Computation
