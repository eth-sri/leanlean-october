/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverGraph
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial




/-- Projection from actual cover neighbors is exactly the four-neighbor base
lattice projection; each projected neighbor has its unique sheet-shifted lift. -/
theorem parafermionicCoverGraph_neighborSet_eq_neighborLift_image
    (u : ParafermionicCoverVertex) :
    parafermionicCoverGraph.neighborSet u =
       parafermionicCoverNeighborLift u  '' squareLattice.neighborSet u.1 := by
  ext w
  constructor
  · intro hw
    have hadj  :=
       by simpa only  using hw 
    
    
    exact ⟨w.1,   by simpa only [SimpleGraph.mem_neighborSet] using hadj.1  , (parafermionicCoverNeighborLift_unique u w.1 w rfl hadj).symm⟩
  · rintro ⟨v, hv, rfl⟩
    
    exact parafermionicCoverNeighborLift_adj u v
      (by simpa only [SimpleGraph.mem_neighborSet] using hv)

end PottsDiscontinuity.TorusTopology.Planar.Medial
