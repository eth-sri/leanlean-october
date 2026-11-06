import Mathlib


/-!
# Walls (hyperplanes) of a simply connected square complex

The remaining geometric input of the paper, in the branch developed in
`RequestProject/CubeCartanHadamard.lean`, `RequestProject/CubeRollerModel.lean` and
`RequestProject/CubeMedianGraph.lean`, is the criterion

> a simply connected cube complex with flag links has median one–skeleton

(Gromov's link condition together with Chepoi's theorem).  Its first half — the half that is
responsible for *hyperplanes*, i.e. for the halfspace (Roller) coordinates used in
`FiniteChains.RollerModel` — is purely combinatorial and is proved here from scratch, with no
finiteness, local finiteness or dimension assumption:

*in a simply connected square complex every square-closed family of edges (in particular every
hyperplane) is two-sided: it is the set of edges joining the two sides of a partition of the
vertex set.*

Everything is elementary and self-contained:

* `FiniteChains.SquareComplex` — a graph together with a set of squares (two-cells), closed under
  rotating and reversing the cyclic order of the four vertices;
* walks are lists of vertices (`List.IsChain S.adj`), and `FiniteChains.SquareComplex.Move` is the
  elementary combinatorial homotopy: cancelling a backtrack `x, y, x ↝ x`, and pushing a path
  across a square `a, b, c ↝ a, d, c`;
* `FiniteChains.SquareComplex.SimplyConnected` says that every closed walk is homotopic to the
  constant walk.

The main results are

* `FiniteChains.SquareComplex.crossings_homotopic` — the number of edges of a walk lying in a
  square-closed family is a homotopy invariant modulo two;
* `FiniteChains.SquareComplex.crossings_eq_zero_of_closed` — hence it vanishes on closed walks of a
  simply connected complex;
* `FiniteChains.SquareComplex.exists_side` — hence, over a connected complex, every square-closed
  family `χ` of edges is the set of edges separating the two sides of a two-colouring `σ` of the
  vertices: `σ u + σ v = χ u v` for every edge `u v`;
* `FiniteChains.SquareComplex.exists_bipartition` — with the family of *all* edges: the
  one-skeleton of a connected simply connected square complex is bipartite (as the one-skeleton of a
  median graph must be);
* `FiniteChains.SquareComplex.closed_walk_length_odd` — equivalently, all closed walks have even
  length;
* `FiniteChains.SquareComplex.exists_side_edge` — an edge lying in no square separates the complex;
* `FiniteChains.SquareComplex.triangle_side_in_square` — hence every triangle has a side lying in a
  square; with the flag/dimension conditions of the cube complexes considered in the paper this is
  the absence of triangles.

Non-vacuity is checked on two explicit complexes: the complex with two vertices and one edge
(`FiniteChains.edgeComplex`) and the four-cycle with its square glued in
(`FiniteChains.cycleFour`, `FiniteChains.cycleFour_simplyConnected`), the latter containing a
genuine two-cell.  That the square is really needed is also checked: the four-cycle *without* the
square is not simply connected (`FiniteChains.cycleFourNoSquare_not_simplyConnected`).
-/
