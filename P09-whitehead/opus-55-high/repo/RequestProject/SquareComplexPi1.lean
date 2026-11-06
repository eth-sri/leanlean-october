import RequestProject.SquareComplexCovering
import RequestProject.SquareComplexTreeCase
import RequestProject.Tac


/-!
# The combinatorial fundamental group of a square complex

This file introduces the edge-path group of a square complex: closed walks based at a vertex,
taken up to the homotopy through walks of
`RequestProject/SquareComplexWalkHomotopy.lean`.

* `FiniteChains.SquareComplex.Pi1` — the group of homotopy classes of closed walks;
* `FiniteChains.SquareComplex.pi1_trivial_iff_simplyConnectedW` — the complex is simply
  connected exactly when this group is trivial;
* `FiniteChains.SquareComplex.IsCovering.liftEnd` — the end point of the lift of a walk of the
  base, and `FiniteChains.SquareComplex.IsCovering.monodromy` — the resulting **monodromy map**
  from `Pi1` of the base to the fibre, which is a bijection as soon as the covering complex is
  connected and simply connected.

Walks are taken in the form of `SimpleGraph.Walk` of the one-skeleton `toSimpleGraph`, so that
concatenation, reversal and their algebraic identities are available; homotopy is compared with
them through `SimpleGraph.Walk.support`.
-/

bwd
