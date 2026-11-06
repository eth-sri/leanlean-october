import RequestProject.SquareComplexWalls


/-!
# The four-cycle with its square: non-vacuity of the wall theorems

`RequestProject/SquareComplexWalls.lean` proves that in a simply connected square complex every
square-closed family of edges is two-sided.  Here the hypotheses are checked on an explicit
complex which really has a two-cell: the four-cycle `ZMod 4` with its square glued in
(`FiniteChains.cycleFour`).  We prove

* `FiniteChains.cycleFour_simplyConnected` — every closed walk contracts by elementary moves, so
  the complex is simply connected (this is where the two-cell is used);
* `FiniteChains.cycleFour_connected` — it is connected;
* `FiniteChains.cycleFour_bipartition`, `FiniteChains.cycleFour_wall` — the conclusions of
  `SquareComplex.exists_bipartition` and `SquareComplex.exists_side` therefore apply to it;
* `FiniteChains.cycleFourNoSquare_not_simplyConnected` — the same graph *without* the two-cell is
  not simply connected, so the two-cell is genuinely needed and the notion of simple connectivity
  used in the wall theorems is not vacuous.
-/
