module

public import RequestProject.CubeCartanHadamard

@[expose] public section

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

namespace FiniteChains

universe u

/-- A **median graph**, recorded through its distance function: a metric with values in `ℕ`
together with a median operation assigning to three vertices the unique vertex lying on a
geodesic between each pair.  `base` is the vertex from which heights are measured, and
`dim_le` says that the complex is at most three dimensional. -/
structure MedianGraph (Vx : Type u) where
  /-- The graph distance. -/
  dist : Vx → Vx → ℕ
  /-- The base vertex. -/
  base : Vx
  dist_self : ∀ x, dist x x = 0
  eq_of_dist_eq_zero : ∀ {x y : Vx}, dist x y = 0 → x = y
  dist_comm : ∀ x y : Vx, dist x y = dist y x
  dist_triangle : ∀ x y z : Vx, dist x z ≤ dist x y + dist y z
  /-- The median of three vertices. -/
  med : Vx → Vx → Vx → Vx
  med_ab : ∀ a b c : Vx, dist a (med a b c) + dist (med a b c) b = dist a b
  med_bc : ∀ a b c : Vx, dist b (med a b c) + dist (med a b c) c = dist b c
  med_ac : ∀ a b c : Vx, dist a (med a b c) + dist (med a b c) c = dist a c
  med_unique : ∀ a b c z : Vx, dist a z + dist z b = dist a b → dist b z + dist z c = dist b c →
    dist a z + dist z c = dist a c → z = med a b c
  /-- The complex is at most three dimensional: a vertex has at most three neighbours closer
  to the base vertex. -/
  dim_le : ∀ (w : Vx) (s : Finset Vx),
    (∀ a ∈ s, dist a w = 1 ∧ dist base a + 1 = dist base w) → s.card ≤ 3

namespace MedianGraph

variable {Vx : Type u} (G : MedianGraph Vx)

variable {G}

variable (G)

end MedianGraph

end FiniteChains
