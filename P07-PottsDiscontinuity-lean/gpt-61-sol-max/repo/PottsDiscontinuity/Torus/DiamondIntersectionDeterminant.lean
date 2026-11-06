module
public import Mathlib

public import PottsDiscontinuity.Torus.DiamondHomologyCoordinates

/-!
# Intersection is the determinant of lifted displacement

Zero displacement is exactly a full-torus cellular boundary. Subtracting the two
explicit displacement classes therefore reduces any cycle to a boundary, giving
the determinant formula for the alternating intersection pairing.
-/

@[expose] public section

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section

variable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
include hNp hMp

theorem fullDiamondDisplacement_eq_zero_iff  (f : diamondCycleSpace hN hM (openRCConfig N M)) :
    fullDiamondDisplacementMap hN hM f = 0 ↔ f ∈ ribbonBoundarySpace hN hM (openRCConfig N M) := by
  constructor
  · intro hf
    
    have hm : f ∈ LinearMap.ker (ribbonBoundarySpace hN hM (openRCConfig N M)).mkQ :=  fullHomologyDisplacementMap_injective hN hM hNp hMp (by
                                                                                           rw [fullHomologyDisplacementMap_mk, hf, map_zero]) 
    simpa only [Submodule.ker_mkQ] using hm
  · intro hf
    exact ribbonBoundarySpace_le_ker_displacement hN hM hf

/-- The full-torus cyclic-order form is the displacement determinant divided by NM. -/
theorem ribbonIntersection_mul_area 
    (f g : diamondCycleSpace hN hM (openRCConfig N M)) :
    (N * M : ℚ) * ribbonIntersection hN hM (openRCConfig N M) f g =
      diamondHorizontalDisplacement (openRCConfig N M) f.val *
        diamondVerticalDisplacement (openRCConfig N M) g.val -
      diamondVerticalDisplacement (openRCConfig N M) f.val *
        diamondHorizontalDisplacement (openRCConfig N M) g.val := by
  let X := diamondHorizontalDisplacement (openRCConfig N M) f.val
  let Y := diamondVerticalDisplacement (openRCConfig N M) f.val
  let L : ℚ := N * M
  have hn : L ≠ 0 := by  positivity
  let r := f + (Y / L) • verticalDiamondCycle hN hM + (X / L) • horizontalDiamondCycle hN hM
  
  have hb := (fullDiamondDisplacement_eq_zero_iff hN hM hNp hMp r).mp (by
                                                                         
                                                                         rw [map_add, map_add, map_smul, map_smul, fullDiamondDisplacementMap_apply,
                                                                           fullDiamondDisplacementMap_vertical, fullDiamondDisplacementMap_horizontal]
                                                                         all_goals aesop)
  have he := ribbonIntersection_zero_of_mem_boundary hN hM (openRCConfig N M) r g hb
  
  rw [ribbonIntersection_add_left, ribbonIntersection_add_left,
    ribbonIntersection_smul_left, ribbonIntersection_smul_left,
    ribbonIntersection_vertical_eq_displacement, ribbonIntersection_horizontal_eq_displacement] at he
  have hm := congrArg (fun z  => L * z) he
  have hx : L * (Y / L * diamondHorizontalDisplacement (openRCConfig N M) g.val) =
      Y * diamondHorizontalDisplacement (openRCConfig N M) g.val := by field_simp
  have hy : L * (X / L * -diamondVerticalDisplacement (openRCConfig N M) g.val) =
      -(X * diamondVerticalDisplacement (openRCConfig N M) g.val) := by field_simp
  
  
  linarith

end

end PottsDiscontinuity.Torus
