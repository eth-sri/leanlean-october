import RequestProject.CubeMedianGraph


/-!
# The median hypothesis as a statement about an actual graph

`RequestProject/CubeMedianGraph.lean` derives the descending-cube axioms — and therefore the
vanishing of the second homology of the cellular chain complex — from the structure
`FiniteChains.MedianGraph`, which records a metric with values in `ℕ` together with a unique
median for every triple.

That structure is deliberately weak: nothing in it says that the metric is the *edge metric*
of a graph, i.e. that the distance between two vertices is the length of a shortest path in
which every step moves along an edge.  This file closes that gap in two directions.

## 1. Genuine median graphs

`FiniteChains.MedianSimpleGraph` records the standard graph-theoretic notion:

* a `SimpleGraph` on the vertex set,
* the hypothesis that it is **connected**, so that `SimpleGraph.dist` really is the length of
  a shortest edge path,
* a base vertex,
* a median operation which is, for that graph distance, the unique vertex lying between each
  pair of the three given vertices,
* the dimension bound stated with the *adjacency relation* of the graph.

`FiniteChains.MedianSimpleGraph.toMedianGraph` shows that such a graph is a `MedianGraph` in
the earlier sense, with `dist` the graph distance.  The audit lemmas

* `FiniteChains.MedianSimpleGraph.dist_eq_one_iff_adj` — the pairs at distance one are exactly
  the edges of the graph, so the one-cells of the derived complex are the graph edges,
* `FiniteChains.MedianSimpleGraph.mem_dnM_iff` — the descending neighbours used by the
  descending-cube axioms are the neighbours of `w` one step closer to the base vertex,
* `FiniteChains.MedianSimpleGraph.exists_walk_length_eq_dist`,
  `FiniteChains.MedianSimpleGraph.exists_geodesic_through_median` — the distance and the
  betweenness relation used in the median axioms are realised by edge paths, each step of
  which changes exactly one coordinate (moves along one edge),

record that the derived combinatorial data is the data of the graph itself.  The conclusion
`FiniteChains.MedianSimpleGraph.ker_d₂_eq_range_d₃` is therefore the vanishing of the second
homology of the cube complex whose one-skeleton is the given median graph.

## 2. Why the extra hypotheses are needed

`FiniteChains.notGraphMetric` exhibits a `MedianGraph` structure whose distance function is
*not* the edge metric of any graph: on a two-element vertex set, the distance `2` between the
two vertices admits a unique median for every triple, yet no vertex is at distance one from
another, so the associated graph has no edges and is disconnected.  This is the reason the
structure `MedianSimpleGraph` carries the graph and its connectivity explicitly, rather than
only an integer-valued metric.
-/
