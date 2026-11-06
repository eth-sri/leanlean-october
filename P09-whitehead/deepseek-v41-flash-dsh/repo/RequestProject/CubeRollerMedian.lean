module

public import RequestProject.CubeRollerModel
public import RequestProject.CubeMedianGraph

@[expose] public section

/-!
# The Roller model is a median graph

`RequestProject/CubeRollerModel.lean` and `RequestProject/CubeMedianGraph.lean` derive the
descending-cube axioms from the two standard combinatorial descriptions of a CAT(0) cube
complex.  This file relates the two descriptions: the vertex set of a Roller model, with the
distance «number of hyperplanes separating two vertices» and the majority operation, *is* a
median graph (`FiniteChains.RollerModel.toMedianGraph`).  In particular the median-graph
axioms are satisfied by a large family of complexes, and the median-graph theorem subsumes
the Roller one.

The combinatorial content is elementary but worth recording:

* `FiniteChains.RollerBridge.dsym_med` — the majority set lies on a geodesic between each pair
  of the three arguments;
* `FiniteChains.RollerBridge.between_of_dsym` — conversely, a vertex on a geodesic from `A` to
  `B` satisfies `A ∩ B ⊆ Z ⊆ A ∪ B`;
* `FiniteChains.RollerBridge.eq_med_of_between` — a vertex between each pair of `A`, `B`, `C`
  is the majority set, so the median is unique.
-/

namespace FiniteChains


namespace RollerBridge

variable {ι : Type u} [DecidableEq ι]

/-- The number of hyperplanes separating two vertices. -/
def dsym (A B : Finset ι) : ℕ := (A \ B).card + (B \ A).card

end RollerBridge

namespace RollerModel

open RollerBridge

variable {ι : Type u} [DecidableEq ι] (M : RollerModel ι)

end RollerModel

end FiniteChains
