import RequestProject.SquareComplexWalls


/-!
# Homotopy through walks

The elementary moves of `FiniteChains.SquareComplex.Move` may be applied to an arbitrary list of
vertices; in particular `Move.backtrack x y q` inserts the detour `x, y, x` even when `x` and `y`
are *not* joined by an edge.  For all the invariants studied in
`RequestProject/SquareComplexWalls.lean` (crossing numbers modulo two) this is harmless, and it
makes the hypothesis `SimplyConnected` weaker, hence the theorems using it stronger.

For lifting homotopies to a covering, however, such detours are genuinely inconvenient: an edge of
the base lifts to an edge of the covering, but a non-edge lifts to nothing.  This file therefore
introduces the homotopy relation in which every intermediate stage is a walk:

* `FiniteChains.SquareComplex.WalkMove` — an elementary move, in either direction, between two
  walks;
* `FiniteChains.SquareComplex.WalkHomotopic` — the equivalence relation it generates;
* `FiniteChains.SquareComplex.SimplyConnectedW` — every closed walk contracts to its base point
  through walks.

The two notions are compared: `WalkHomotopic.homotopic` and `SimplyConnectedW.simplyConnected`
show that the new relation is finer, so every result proved for `SimplyConnected` complexes
applies to `SimplyConnectedW` ones.
-/
