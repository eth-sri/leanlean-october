module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

def parafermionicCoverFaceRightLift (x y k : ℤ) : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift ((x,y),k) (x+1,y)

def parafermionicCoverFaceRightUpLift (x y k : ℤ) : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift (parafermionicCoverFaceRightLift x y k) (x+1,y+1)

def parafermionicCoverFaceRightUpLeftLift (x y k : ℤ) : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift (parafermionicCoverFaceRightUpLift x y k) (x,y+1)

def parafermionicCoverFaceLiftEndpoint (x y k : ℤ) : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift (parafermionicCoverFaceRightUpLeftLift x y k) (x,y)

theorem parafermionicCoverFaceLift_steps_adj (x y k : ℤ) :
    parafermionicCoverGraph.Adj ((x,y),k) (parafermionicCoverFaceRightLift x y k) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverFaceRightLift x y k)
      (parafermionicCoverFaceRightUpLift x y k) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverFaceRightUpLift x y k)
      (parafermionicCoverFaceRightUpLeftLift x y k) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverFaceRightUpLeftLift x y k)
      (parafermionicCoverFaceLiftEndpoint x y k) :=
  ⟨parafermionicCoverNeighborLift_adj _ _ (by rw [squareLattice_adj_iff]; left; exact ⟨Or.inl rfl, rfl⟩),
   parafermionicCoverNeighborLift_adj _ _ (by rw [squareLattice_adj_iff]; right; exact ⟨rfl, Or.inl rfl⟩),
   parafermionicCoverNeighborLift_adj _ _ (by rw [squareLattice_adj_iff]; left; exact ⟨Or.inr rfl, rfl⟩),
   parafermionicCoverNeighborLift_adj _ _ (by rw [squareLattice_adj_iff]; right; exact ⟨rfl, Or.inr rfl⟩)⟩

theorem parafermionicCoverFaceLiftEndpoint_eq_start (x y k : ℤ) :
    parafermionicCoverFaceLiftEndpoint x y k = ((x,y),k) := by
  simp [parafermionicCoverFaceLiftEndpoint, parafermionicCoverFaceRightUpLeftLift,
    parafermionicCoverFaceRightUpLift, parafermionicCoverFaceRightLift,
    parafermionicCoverNeighborLift, parafermionicCoverSheetShift]

end PottsDiscontinuity.TorusTopology.Planar.Medial
