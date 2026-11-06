module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaces
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

@[simp] theorem parafermionicCoverFaceRightLift_formula (x y k : ℤ) :
    parafermionicCoverFaceRightLift x y k = ((x+1,y), k) := by
  simp [parafermionicCoverFaceRightLift, parafermionicCoverNeighborLift, parafermionicCoverSheetShift]

@[simp] theorem parafermionicCoverFaceRightUpLift_formula (x y k : ℤ) :
    parafermionicCoverFaceRightUpLift x y k = ((x+1,y+1), k) := by
  simp [parafermionicCoverFaceRightUpLift, parafermionicCoverNeighborLift, parafermionicCoverSheetShift]

@[simp] theorem parafermionicCoverFaceRightUpLeftLift_formula (x y k : ℤ) :
    parafermionicCoverFaceRightUpLeftLift x y k = ((x,y+1), k) := by
  simp [parafermionicCoverFaceRightUpLeftLift, parafermionicCoverNeighborLift, parafermionicCoverSheetShift]

def parafermionicCoverFiniteOrdinaryFaces (n : ℕ) :
    Finset ParafermionicCoverVertex :=
  (parafermionicCoverBoxFinset n).filter fun v =>
    parafermionicCoverFaceRightLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ∧
    parafermionicCoverFaceRightUpLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ∧
    parafermionicCoverFaceRightUpLeftLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n

theorem parafermionicCoverFaceIntermediateBounds_iff (n : ℕ)
    (v : ParafermionicCoverVertex) :
    v ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLeftLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ↔
    -(n : ℤ) ≤ v.1.1 ∧ v.1.1 < (n : ℤ) ∧
      -(n : ℤ) ≤ v.1.2 ∧ v.1.2 < (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ v.2 ∧ v.2 ≤ ((n ^ 5 : ℕ) : ℤ) := by
  rcases v with ⟨⟨x, y⟩, k⟩
  simp only [parafermionicCoverFaceRightLift_formula, parafermionicCoverFaceRightUpLift_formula,
    parafermionicCoverFaceRightUpLeftLift_formula, parafermionicCoverBoxVertices_mem]
  omega

theorem parafermionicCoverFiniteOrdinaryFaces_mem_iff (n : ℕ)
    (v : ParafermionicCoverVertex) :
    v ∈ parafermionicCoverFiniteOrdinaryFaces n ↔
      -(n : ℤ) ≤ v.1.1 ∧ v.1.1 < (n : ℤ) ∧
      -(n : ℤ) ≤ v.1.2 ∧ v.1.2 < (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ v.2 ∧ v.2 ≤ ((n ^ 5 : ℕ) : ℤ) := by
  rw [parafermionicCoverFiniteOrdinaryFaces, Finset.mem_filter]
  exact parafermionicCoverFaceIntermediateBounds_iff n v

end PottsDiscontinuity.TorusTopology.Planar.Medial
