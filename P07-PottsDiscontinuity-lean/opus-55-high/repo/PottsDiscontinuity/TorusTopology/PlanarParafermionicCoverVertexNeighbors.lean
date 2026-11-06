/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverGraph
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

/-- Projection from actual cover neighbors is exactly the four-neighbor base
lattice projection; each projected neighbor has its unique sheet-shifted lift. -/
theorem parafermionicCoverGraph_neighborSet_eq_neighborLift_image
    (u : ParafermionicCoverVertex) :
    parafermionicCoverGraph.neighborSet u =
      (parafermionicCoverNeighborLift u) '' squareLattice.neighborSet u.1 := by
  ext w
  constructor
  · intro hw
    have hadj : parafermionicCoverGraph.Adj u w :=
      by simp_all
    have hbase : w.1 ∈ squareLattice.neighborSet u.1 :=
      (by simpa using hadj.1)
    have hlift := parafermionicCoverNeighborLift_unique u w.1 w rfl hadj
    grind
  · rintro ⟨v, hv, rfl⟩
    tauto

end PottsDiscontinuity.TorusTopology.Planar.Medial
