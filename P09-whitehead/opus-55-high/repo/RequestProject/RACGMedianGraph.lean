import RequestProject.RACGMedian
import RequestProject.CubeMedianGraph


/-!
# The Cayley graph of a right-angled Coxeter group is a median graph

This file assembles `RequestProject/RACGMedian.lean` into the interface
`FiniteChains.MedianGraph` used by `RequestProject/CubeMedianGraph.lean`, that is, into the
CAT(0) input of the paper in its standard combinatorial form.

* `FiniteChains.RACG.medianGraph` — for a commutation graph without cliques of four vertices
  (equivalently: for a cube complex of dimension at most three) the Cayley graph of the
  right-angled Coxeter group, with the word metric, is a median graph;
* `FiniteChains.RACG.cycles_bound` — consequently every two-cycle of its cellular chain complex
  bounds, which is exactly the vanishing `H₂(V) = 0` used in the generation lemma of the paper.

Together with `RequestProject/MedianSimplyConnected.lean` (the converse implication: the square
complex of a median graph is simply connected with flag links) this makes Gromov's criterion a
theorem for the cube complexes `C(L)` of the paper: the one-skeleton of the universal cover of
`C(L)` is the Cayley graph above.
-/
