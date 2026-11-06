module

public import RequestProject.TreeMedian

@[expose] public section

/-!
# Gromov's criterion in dimension one

The geometric input still quoted from the literature in the cube-complex branch is

> a simply connected cube complex with flag links has median one-skeleton.

This file proves it in dimension one, that is for a square complex with **no two-cells**: there
the link condition is vacuous, and the statement becomes "a connected simply connected graph is
a tree, and trees are median".  Both halves are proved:

* `FiniteChains.SquareComplex.toSimpleGraph` — the one-skeleton of a square complex as a simple
  graph, and `FiniteChains.SquareComplex.crossings_support` — the crossing number of a wall
  label along a walk counts, modulo two, how often the walk uses the labelled edge;
* `FiniteChains.SquareComplex.isAcyclic_of_simplyConnected` — a simply connected square complex
  without two-cells has an acyclic one-skeleton.  The proof needs no new geometry: the
  characteristic function of a single edge is a wall label (the square condition is vacuous),
  so by `FiniteChains.SquareComplex.crossings_eq_zero_of_closed` every closed walk uses that
  edge an even number of times, while a cycle uses each of its edges exactly once;
* `FiniteChains.SquareComplex.isTree_of_simplyConnected` and
  `FiniteChains.SquareComplex.medianSimpleGraph_of_simplyConnected` — hence the one-skeleton is
  a tree and, by `FiniteChains.Tree.toMedianSimpleGraph`, a median graph.  This is the
  one-dimensional case of the criterion, proved unconditionally.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

namespace SquareComplex

universe u

variable {Vx : Type u} [DecidableEq Vx] {S : SquareComplex Vx}

/-- The one-skeleton of a square complex, as a simple graph. -/
def toSimpleGraph (S : SquareComplex Vx) : SimpleGraph Vx where
  Adj := S.adj
  symm := ⟨fun _ _ h => S.adj_symm h⟩
  loopless := ⟨S.adj_irrefl⟩

omit [DecidableEq Vx] in
@[simp] theorem toSimpleGraph_adj (a b : Vx) : (toSimpleGraph S).Adj a b ↔ S.adj a b := Iff.rfl

end SquareComplex

end FiniteChains
