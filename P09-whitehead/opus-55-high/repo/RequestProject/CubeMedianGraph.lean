import RequestProject.CubeCartanHadamard


/-!
# Median graphs and the descending-cube axioms

`RequestProject/CubeCartanHadamard.lean` proves `H₂ = 0` for the cellular chains of an at most
three-dimensional cube complex satisfying the descending-cube axioms
(`FiniteChains.DescCubeStr`).  `RequestProject/CubeRollerModel.lean` derives those axioms from
the Roller (halfspace) description of a CAT(0) cube complex.  This file derives them from the
other standard combinatorial description: the one-skeleton of a CAT(0) cube complex is a
*median graph*, that is, a graph in which any three vertices have a unique median — a vertex
lying simultaneously on a geodesic between each pair.

The structure `FiniteChains.MedianGraph` records exactly this, the graph being given through
its distance function:

* a metric `dist` with values in `ℕ` (edges are the pairs at distance one);
* a base vertex;
* a median operation `med`, with the statement that `med a b c` lies on a geodesic between
  each pair and that it is the only vertex that does;
* the dimension bound: a vertex has at most three descending neighbours.

Everything else is proved:

* `FiniteChains.MedianGraph.dist_eq_two_of_common_neighbour` — a median graph has no
  triangles: two distinct vertices with a common neighbour are at distance two;
* `FiniteChains.MedianGraph.not_three_common_neighbours` — a median graph has no `K₂,₃`;
* `FiniteChains.MedianGraph.med_square` — two descending edges at a vertex span a square;
* `FiniteChains.MedianGraph.med_ne_med` — distinct pairs of descending edges span distinct
  squares;
* `FiniteChains.MedianGraph.med_bottom` — three descending edges at a vertex span a
  three-cube (the *cube condition*), which is the combinatorial content of the CAT(0)
  (Cartan–Hadamard) input of the paper;
* `FiniteChains.MedianGraph.toDescCubeStr` — hence all the descending-cube axioms hold, and
* `FiniteChains.MedianGraph.exists_d₃_eq`, `FiniteChains.MedianGraph.ker_d₂_eq_range_d₃` —
  hence every two-cycle of the cellular chain complex bounds.
-/
