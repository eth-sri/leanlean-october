import RequestProject.SquareComplexWalls
import RequestProject.WallSpaceDualConnected


/-!
# From the walls of a square complex to a wall space

`RequestProject/SquareComplexWalls.lean` produces, for a connected and simply connected square
complex carrying a system of walls, halfspace coordinates `σ i : Vx → ZMod 2`: each wall cuts
the vertex set into two sides, an edge changes exactly one coordinate, and only finitely many
walls separate two given vertices.  `RequestProject/WallSpaceDual.lean` shows that a *wall
space* has a median dual cube complex.

This file joins the two halves.  The single missing ingredient is the *separation* property —
distinct vertices are separated by some wall — which is exactly the part of Sageev's theorem
that is not proved in the project; it is therefore carried here as an explicit hypothesis.
Granting it:

* `FiniteChains.SquareComplex.wallSpaceOf` — the vertices, with the walls, form a
  `FiniteChains.WallSpace`;
* `FiniteChains.SquareComplex.wallSpaceOf_coord_injective` — the vertices embed into the
  median dual complex;
* `FiniteChains.SquareComplex.wallSpaceOf_dsym_adj` — an edge of the complex becomes an edge
  of the dual: the halfspace coordinates of its endpoints differ in exactly one wall.

Thus, granting separation, the one-skeleton of such a complex maps injectively and
edge-preservingly into a median (CAT(0) cube complex) graph.
-/
