module

public import RequestProject.CubeRollerMedian
public import RequestProject.MedianGraphMetric
public import RequestProject.RollerConnected

@[expose] public section

/-!
# The Roller model as an actual graph

`RequestProject/CubeRollerMedian.lean` shows that the vertex set of a median-closed Roller
model, with the distance `dsym A B = |A \ B| + |B \ A|` counting the separating hyperplanes, is
a `FiniteChains.MedianGraph`: a metric with unique medians.  As `RequestProject/RollerConnected.lean`
records, median-closedness alone does not make that metric the edge metric of a graph — the
median-closed set `{∅, {p, q}}` has no one-coordinate path between its two vertices.

This file adds the hypothesis that makes the model a genuine graph and proves the resulting
statement.  A `FiniteChains.GatedRollerModel` is a Roller model in which, for any two distinct
vertices `A ≠ B`, some vertex `C` of the model is obtained from `A` by changing one coordinate
and is one step closer to `B` (a *gate* step towards `B`).  Then:

* `FiniteChains.GatedRollerModel.graph` — the graph whose edges are the pairs of vertices
  differing in exactly one hyperplane;
* `FiniteChains.GatedRollerModel.dist_eq_dsym` — the graph distance of that graph is exactly
  the number of separating hyperplanes, so `dsym` is the edge metric;
* `FiniteChains.GatedRollerModel.connected` — the graph is connected;
* `FiniteChains.GatedRollerModel.toMedianSimpleGraph` — the model is a median graph in the
  graph-theoretic sense of `RequestProject/MedianGraphMetric.lean`;
* `FiniteChains.GatedRollerModel.ker_d₂_eq_range_d₃` — hence `ker d₂ = im d₃` for the cellular
  chains, with all the cells being genuine cubes of that graph.
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains

open RollerBridge


variable {ι : Type u} [DecidableEq ι]

/-- A **gated Roller model**: a median-closed Roller model in which one can always move one
step towards another vertex by changing a single coordinate.  This is what makes the counting
distance `dsym` the edge metric of a connected graph. -/
structure GatedRollerModel (ι : Type u) [DecidableEq ι] extends RollerModel ι where
  /-- From any vertex one can step towards any other vertex, changing one coordinate. -/
  step : ∀ {A B : Finset ι}, A ∈ toRollerModel.W → B ∈ toRollerModel.W → A ≠ B →
    ∃ C ∈ toRollerModel.W, dsym A C = 1 ∧ dsym C B + 1 = dsym A B

namespace GatedRollerModel

variable (M : GatedRollerModel ι)

end GatedRollerModel

end FiniteChains
