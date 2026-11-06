/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverGraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

section
variable (x y k : ℤ)
/-- The actual lift after taking the right edge of a positively oriented unit face. -/
def parafermionicCoverFaceRightLift  : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift ((x,y),k) (x+1,y)

/-- Continue the same lifted face traversal upward. -/
def parafermionicCoverFaceRightUpLift  : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift (parafermionicCoverFaceRightLift x y k) (x+1,y+1)

/-- Continue the same lifted face traversal to the left. -/
def parafermionicCoverFaceRightUpLeftLift  : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift (parafermionicCoverFaceRightUpLift x y k) (x,y+1)

/-- The endpoint after the four actual lifts around a unit square. -/
def parafermionicCoverFaceLiftEndpoint  : ParafermionicCoverVertex :=
  parafermionicCoverNeighborLift (parafermionicCoverFaceRightUpLeftLift x y k) (x,y)
end

section
variable (x y : ℤ)
theorem coverFace_base_right  :
    squareLattice.Adj (x,y) (x+1,y) := by
  tauto

theorem coverFace_base_up  :
    squareLattice.Adj (x+1,y) (x+1,y+1) := by
  tauto

theorem coverFace_base_left  :
    squareLattice.Adj (x+1,y+1) (x,y+1) := by
  tauto

theorem coverFace_base_down  :
    squareLattice.Adj (x,y+1) (x,y) := by
  tauto
end

section
variable (x y k : ℤ)
/-- The four successive lifts are actual edges of the cover graph in the stated
right/up/left/down order. -/
theorem parafermionicCoverFaceLift_steps_adj  :
    parafermionicCoverGraph.Adj ((x,y),k) (parafermionicCoverFaceRightLift x y k) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverFaceRightLift x y k)
      (parafermionicCoverFaceRightUpLift x y k) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverFaceRightUpLift x y k)
      (parafermionicCoverFaceRightUpLeftLift x y k) ∧
    parafermionicCoverGraph.Adj (parafermionicCoverFaceRightUpLeftLift x y k)
      (parafermionicCoverFaceLiftEndpoint x y k) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact parafermionicCoverNeighborLift_adj ((x,y),k) (x+1,y)
      (coverFace_base_right x y)
  · exact parafermionicCoverNeighborLift_adj
      (parafermionicCoverFaceRightLift x y k) (x+1,y+1)
      (coverFace_base_up x y)
  · exact parafermionicCoverNeighborLift_adj
      (parafermionicCoverFaceRightUpLift x y k) (x,y+1)
      (coverFace_base_left x y)
  · exact parafermionicCoverNeighborLift_adj
      (parafermionicCoverFaceRightUpLeftLift x y k) (x,y)
      (coverFace_base_down x y)

theorem parafermionicCoverFaceLiftEndpoint_formula  :
    parafermionicCoverFaceLiftEndpoint x y k =
      ((x,y), k + if (x,y) = (0,-1) then 1 else 0) := by
  simp [parafermionicCoverFaceLiftEndpoint,
    parafermionicCoverFaceRightUpLeftLift,
    parafermionicCoverFaceRightUpLift,
    parafermionicCoverFaceRightLift,
    parafermionicCoverNeighborLift,
    parafermionicCoverSheetShift]
  grind

theorem parafermionicCoverFaceLiftEndpoint_eq_start_of_not_branch
    (h : (x,y) ≠ (0,-1)) :
    parafermionicCoverFaceLiftEndpoint x y k = ((x,y),k) := by
  simp_all [parafermionicCoverFaceLiftEndpoint_formula]
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
