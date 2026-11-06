/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaces
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section

variable (x y : ℤ)


private theorem coverFace_shift_right  :
    parafermionicCoverSheetShift (x,y) (x+1,y) =
      if x = 0 ∧ y < 0 then 1 else 0 := by
  grind [parafermionicCoverSheetShift]

private theorem coverFace_shift_up  :
    parafermionicCoverSheetShift (x+1,y) (x+1,y+1) = 0 := by
  unfold parafermionicCoverSheetShift
  simp

private theorem coverFace_shift_left  :
    parafermionicCoverSheetShift (x+1,y+1) (x,y+1) =
      if x = 0 ∧ y+1 < 0 then -1 else 0 := by
  grind [parafermionicCoverSheetShift]



end

@[simp] theorem parafermionicCoverFaceRightLift_formula (x y k : ℤ) :
    parafermionicCoverFaceRightLift x y k =
      ((x+1,y), k + if x = 0 ∧ y < 0 then 1 else 0) := by
  simp [parafermionicCoverFaceRightLift, parafermionicCoverNeighborLift,
    coverFace_shift_right]

@[simp] theorem parafermionicCoverFaceRightUpLift_formula (x y k : ℤ) :
    parafermionicCoverFaceRightUpLift x y k =
      ((x+1,y+1), k + if x = 0 ∧ y < 0 then 1 else 0) := by
  simp [parafermionicCoverFaceRightUpLift, parafermionicCoverNeighborLift, coverFace_shift_right, coverFace_shift_up]

@[simp] theorem parafermionicCoverFaceRightUpLeftLift_formula (x y k : ℤ) :
    parafermionicCoverFaceRightUpLeftLift x y k =
      ((x,y+1), k + (if x = 0 ∧ y < 0 then 1 else 0) +
         if x = 0 ∧ y+1 < 0 then -1 else 0 ) := by
  simp [parafermionicCoverFaceRightUpLeftLift, parafermionicCoverNeighborLift, coverFace_shift_right, coverFace_shift_up, coverFace_shift_left]

private theorem parafermionicCoverBox_coords (n : ℕ) (x y k : ℤ) :
    ((x,y),k) ∈ parafermionicCoverBoxVertices n ↔
      -(n : ℤ) ≤ x ∧ x ≤ (n : ℤ) ∧
      -(n : ℤ) ≤ y ∧ y ≤ (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ) := by
  rw [parafermionicCoverBoxVertices_mem]

/-- Literal finite carrier of ordinary unit faces: the lower-left lifted vertex
and each of the three intermediate vertices of its actual lift lie in `U_n`.
The puncture face is excluded. -/
def parafermionicCoverFiniteOrdinaryFaces (n : ℕ)  :=
  (parafermionicCoverBoxFinset n).filter fun v =>
    v.1 ≠ (0,-1) ∧
      parafermionicCoverFaceRightLift v.1.1 v.1.2 v.2 ∈
        parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLift v.1.1 v.1.2 v.2 ∈
        parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLeftLift v.1.1 v.1.2 v.2 ∈
        parafermionicCoverBoxVertices n

theorem parafermionicCoverFaceIntermediateBounds_iff (n : ℕ)
    (v : ParafermionicCoverVertex) :
    v ∈ parafermionicCoverBoxVertices n ∧
      v.1 ≠ (0,-1) ∧
      parafermionicCoverFaceRightLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLeftLift v.1.1 v.1.2 v.2 ∈ parafermionicCoverBoxVertices n ↔
    -(n : ℤ) ≤ v.1.1 ∧ v.1.1 < (n : ℤ) ∧
      -(n : ℤ) ≤ v.1.2 ∧ v.1.2 < (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ v.2 ∧ v.2 ≤ ((n ^ 5 : ℕ) : ℤ) ∧
      v.1 ≠ (0,-1) ∧
      (v.1.1 = 0 ∧ v.1.2 < -1 → v.2 < ((n ^ 5 : ℕ) : ℤ)) := by
  rcases v with ⟨⟨x,y⟩,k⟩
  simp only at *
  
  constructor
  · rintro ⟨hstart,hnot,hright,hup,hleft⟩
    have hs := (parafermionicCoverBox_coords n x y k).mp hstart
    
    have hu := (parafermionicCoverBox_coords n (x+1) (y+1)
      (k +  if x = 0 ∧ y < 0 then 1 else 0 )).mp (by
        simpa using hup)
    grind
  · rintro ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hnot,hseam⟩
    
    
    
    
    
    
    exact ⟨ (parafermionicCoverBox_coords n x y k).mpr
                ⟨hxlo,by omega,hylo,by omega,hklo,hkhi⟩ ,hnot, by
                          grind [parafermionicCoverFaceRightLift_formula, parafermionicCoverBox_coords] , by
                                 grind [parafermionicCoverFaceRightUpLift_formula, parafermionicCoverBox_coords] , by
                                     grind [parafermionicCoverFaceRightUpLeftLift_formula, parafermionicCoverBox_coords] ⟩

theorem parafermionicCoverFiniteOrdinaryFaces_mem_iff (n : ℕ)
    (v : ParafermionicCoverVertex) :
    v ∈ parafermionicCoverFiniteOrdinaryFaces n ↔
      -(n : ℤ) ≤ v.1.1 ∧ v.1.1 < (n : ℤ) ∧
      -(n : ℤ) ≤ v.1.2 ∧ v.1.2 < (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ v.2 ∧ v.2 ≤ ((n ^ 5 : ℕ) : ℤ) ∧
      v.1 ≠ (0,-1) ∧
      (v.1.1 = 0 ∧ v.1.2 < -1 → v.2 < ((n ^ 5 : ℕ) : ℤ)) := by
  
  rw [parafermionicCoverFiniteOrdinaryFaces, Finset.mem_filter]
  
  exact  parafermionicCoverFaceIntermediateBounds_iff n v 

end PottsDiscontinuity.TorusTopology.Planar.Medial
