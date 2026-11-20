module

public import RequestProject.CubeMedianGraph

@[expose] public section

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

namespace FiniteChains

universe u

open SimpleGraph

/-- A **median graph** in the graph-theoretic sense: a connected simple graph, with the
distance being the number of edges of a shortest path, in which any three vertices have a
unique median.  `dim_le` is the dimension bound (a vertex has at most three neighbours closer
to the base vertex); it is stated with the adjacency relation of the graph. -/
structure MedianSimpleGraph (Vx : Type u) where
  /-- The graph. -/
  G : SimpleGraph Vx
  /-- The graph is connected, so that `G.dist` is the length of a shortest edge path. -/
  conn : G.Connected
  /-- The base vertex. -/
  base : Vx
  /-- The median of three vertices. -/
  med : Vx → Vx → Vx → Vx
  med_ab : ∀ a b c : Vx, G.dist a (med a b c) + G.dist (med a b c) b = G.dist a b
  med_bc : ∀ a b c : Vx, G.dist b (med a b c) + G.dist (med a b c) c = G.dist b c
  med_ac : ∀ a b c : Vx, G.dist a (med a b c) + G.dist (med a b c) c = G.dist a c
  med_unique : ∀ a b c z : Vx, G.dist a z + G.dist z b = G.dist a b →
    G.dist b z + G.dist z c = G.dist b c → G.dist a z + G.dist z c = G.dist a c → z = med a b c
  /-- The complex is at most three dimensional: a vertex has at most three neighbours closer
  to the base vertex. -/
  dim_le : ∀ (w : Vx) (s : Finset Vx),
    (∀ a ∈ s, G.Adj a w ∧ G.dist base a + 1 = G.dist base w) → s.card ≤ 3

namespace MedianSimpleGraph

variable {Vx : Type u} (M : MedianSimpleGraph Vx)

/-- A median graph, viewed as a metric with a unique median: the distance is the graph
distance, and the edges are exactly the pairs at distance one
(`MedianSimpleGraph.dist_eq_one_iff_adj`). -/
noncomputable def toMedianGraph : MedianGraph Vx where
  dist := M.G.dist
  base := M.base
  dist_self := fun _ => SimpleGraph.dist_self
  eq_of_dist_eq_zero := by
    intro x y h
    rcases SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable.mp h with h | h
    · exact h
    · exact absurd (M.conn.preconnected x y) h
  dist_comm := fun _ _ => SimpleGraph.dist_comm
  dist_triangle := fun _ _ _ => M.conn.dist_triangle
  med := M.med
  med_ab := M.med_ab
  med_bc := M.med_bc
  med_ac := M.med_ac
  med_unique := M.med_unique
  dim_le := by
    intro w s hs
    refine M.dim_le w s fun a ha => ⟨?_, (hs a ha).2⟩
    exact SimpleGraph.dist_eq_one_iff_adj.mp (hs a ha).1

@[simp] theorem toMedianGraph_dist (x y : Vx) : M.toMedianGraph.dist x y = M.G.dist x y := rfl

@[simp] theorem toMedianGraph_base : M.toMedianGraph.base = M.base := rfl

end MedianSimpleGraph

end FiniteChains
