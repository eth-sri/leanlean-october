import RequestProject.SquareComplexMonodromy
import RequestProject.SquareComplexUniversalCover
import RequestProject.Tac


/-!
# Existence of the universal cover of a square complex

`RequestProject/SquareComplexUniversalCover.lean` proves that a connected, simply connected
covering of a square complex is unique up to isomorphism over the base.  This file constructs
one, so that the universal cover exists for every square complex:

* `FiniteChains.SquareComplex.UnivVx` — the vertices are pairs (a vertex `y`, a homotopy class
  of walks from the base point to `y`);
* `FiniteChains.SquareComplex.univCover` — the square complex structure: an edge joins two
  classes when one is obtained from the other by appending an edge, and a square is a square of
  the base whose four corners are joined in this way;
* `FiniteChains.SquareComplex.isCovering_univProj` — the projection to the base is a covering;
* `FiniteChains.SquareComplex.univCover_walkConnected`,
  `FiniteChains.SquareComplex.univCover_simplyConnectedW` — it is connected and simply connected;
* `FiniteChains.SquareComplex.exists_universal_cover` — hence every square complex has a
  connected, simply connected covering, which by
  `FiniteChains.SquareComplex.exists_iso_of_universal` is unique over the base.
-/

bwd
