/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaces
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar

section
variable (x y : ℤ)
theorem coverFace_shift_right  :
    parafermionicCoverSheetShift (x,y) (x+1,y) =
      if x = 0 ∧ y < 0 then 1 else 0 := by
  grind [parafermionicCoverSheetShift]

theorem coverFace_shift_up  :
    parafermionicCoverSheetShift (x+1,y) (x+1,y+1) = 0 := by
  unfold parafermionicCoverSheetShift
  simp

theorem coverFace_shift_left  :
    parafermionicCoverSheetShift (x+1,y+1) (x,y+1) =
      if x = 0 ∧ y+1 < 0 then -1 else 0 := by
  grind [parafermionicCoverSheetShift]
end


section
variable (x y k : ℤ)
@[simp] theorem parafermionicCoverFaceRightLift_formula  :
    parafermionicCoverFaceRightLift x y k =
      ((x+1,y), k + if x = 0 ∧ y < 0 then 1 else 0) := by
  simp [parafermionicCoverFaceRightLift, parafermionicCoverNeighborLift,
    coverFace_shift_right]

@[simp] theorem parafermionicCoverFaceRightUpLift_formula  :
    parafermionicCoverFaceRightUpLift x y k =
      ((x+1,y+1), k + if x = 0 ∧ y < 0 then 1 else 0) := by
  simp [parafermionicCoverFaceRightUpLift, parafermionicCoverFaceRightLift,
    parafermionicCoverNeighborLift, coverFace_shift_right, coverFace_shift_up]

@[simp] theorem parafermionicCoverFaceRightUpLeftLift_formula  :
    parafermionicCoverFaceRightUpLeftLift x y k =
      ((x,y+1), k + (if x = 0 ∧ y < 0 then 1 else 0) +
        (if x = 0 ∧ y+1 < 0 then -1 else 0)) := by
  simp [parafermionicCoverFaceRightUpLeftLift,
    parafermionicCoverFaceRightUpLift, parafermionicCoverFaceRightLift,
    parafermionicCoverNeighborLift, coverFace_shift_right, coverFace_shift_up,
    coverFace_shift_left]
end

section
variable (n : ℕ)
theorem parafermionicCoverBox_coords (x y k : ℤ) :
    ((x,y),k) ∈ parafermionicCoverBoxVertices n ↔
      -(n : ℤ) ≤ x ∧ x ≤ (n : ℤ) ∧
      -(n : ℤ) ≤ y ∧ y ≤ (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ k ∧ k ≤ ((n ^ 5 : ℕ) : ℤ) := by
  rw [parafermionicCoverBoxVertices_mem]

/-- Literal finite carrier of ordinary unit faces: the lower-left lifted vertex
and each of the three intermediate vertices of its actual lift lie in `U_n`.
The puncture face is excluded. -/
def parafermionicCoverFiniteOrdinaryFaces  :
    Finset ParafermionicCoverVertex :=
  (parafermionicCoverBoxFinset n).filter fun v =>
    v.1 ≠ (0,-1) ∧
      parafermionicCoverFaceRightLift v.1.1 v.1.2 v.2 ∈
        parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLift v.1.1 v.1.2 v.2 ∈
        parafermionicCoverBoxVertices n ∧
      parafermionicCoverFaceRightUpLeftLift v.1.1 v.1.2 v.2 ∈
        parafermionicCoverBoxVertices n

theorem parafermionicCoverFaceIntermediateBounds_iff (v : ParafermionicCoverVertex) :
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
  simp at *
  constructor
  · rintro ⟨hstart,hnot,hright,hup,hleft⟩
    have hs := (parafermionicCoverBox_coords n x y k).mp hstart
    have hu := (parafermionicCoverBox_coords n (x+1) (y+1)
      (k + (if x = 0 ∧ y < 0 then 1 else 0))).mp (by
        simp_all)
    grind
  · rintro ⟨hxlo,hxhi,hylo,hyhi,hklo,hkhi,hnot,hseam⟩
    have hstart :=
      (parafermionicCoverBox_coords n x y k).mpr
        ⟨hxlo,by omega,hylo,by omega,hklo,hkhi⟩
    have hright : parafermionicCoverFaceRightLift x y k ∈
        parafermionicCoverBoxVertices n := by
      grind [parafermionicCoverFaceRightLift_formula, parafermionicCoverBox_coords]
    have hup : parafermionicCoverFaceRightUpLift x y k ∈
        parafermionicCoverBoxVertices n := by
      grind [parafermionicCoverFaceRightUpLift_formula, parafermionicCoverBox_coords]
    have hleft : parafermionicCoverFaceRightUpLeftLift x y k ∈
        parafermionicCoverBoxVertices n := by
      grind [parafermionicCoverFaceRightUpLeftLift_formula, parafermionicCoverBox_coords]
    simp_all

theorem parafermionicCoverFiniteOrdinaryFaces_mem_iff (v : ParafermionicCoverVertex) :
    v ∈ parafermionicCoverFiniteOrdinaryFaces n ↔
      -(n : ℤ) ≤ v.1.1 ∧ v.1.1 < (n : ℤ) ∧
      -(n : ℤ) ≤ v.1.2 ∧ v.1.2 < (n : ℤ) ∧
      -((n ^ 5 : ℕ) : ℤ) ≤ v.2 ∧ v.2 ≤ ((n ^ 5 : ℕ) : ℤ) ∧
      v.1 ≠ (0,-1) ∧
      (v.1.1 = 0 ∧ v.1.2 < -1 → v.2 < ((n ^ 5 : ℕ) : ℤ)) := by
  rw [parafermionicCoverFiniteOrdinaryFaces, Finset.mem_filter]
  exact (parafermionicCoverFaceIntermediateBounds_iff n v)
end

end PottsDiscontinuity.TorusTopology.Planar.Medial
