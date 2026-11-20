module

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

variable (hN : Even N) (hM : Even M) (hNp : 0 < N) (hMp : 0 < M)
include hNp hMp

theorem fullDiamondDisplacement_eq_zero_iff (f : diamondCycleSpace hN hM (openRCConfig N M)) :
    fullDiamondDisplacementMap hN hM f = 0 ↔ f ∈ ribbonBoundarySpace hN hM (openRCConfig N M) := by
  constructor
  · intro hf
    have he : (ribbonBoundarySpace hN hM (openRCConfig N M)).mkQ f = 0 :=
      fullHomologyDisplacementMap_injective hN hM hNp hMp (by
        rw [fullHomologyDisplacementMap_mk, hf, map_zero])
    simp_all
  · intro hf
    exact ribbonBoundarySpace_le_ker_displacement hN hM hf

/-- The full-torus cyclic-order form is the displacement determinant divided by NM. -/
theorem ribbonIntersection_mul_area
    (f g : diamondCycleSpace hN hM (openRCConfig N M)) :
    (N * M : ℚ) * ribbonIntersection f g =
      diamondHorizontalDisplacement f.val *
        diamondVerticalDisplacement g.val -
      diamondVerticalDisplacement f.val *
        diamondHorizontalDisplacement g.val := by
  let X := diamondHorizontalDisplacement f.val
  let Y := diamondVerticalDisplacement f.val
  let L : ℚ := N * M
  have hn : L ≠ 0 := by positivity
  let r := f + (Y / L) • verticalDiamondCycle hN hM + (X / L) • horizontalDiamondCycle hN hM
  have hr : fullDiamondDisplacementMap hN hM r = 0 := by
    rw [map_add, map_add, map_smul, map_smul, fullDiamondDisplacementMap_apply,
      fullDiamondDisplacementMap_vertical, fullDiamondDisplacementMap_horizontal]
    simp_all [X, Y, L]
  have hb := (fullDiamondDisplacement_eq_zero_iff hN hM hNp hMp r).mp hr
  have he := ribbonIntersection_zero_of_mem_boundary r g hb
  rw [ribbonIntersection_add_left, ribbonIntersection_add_left,
    ribbonIntersection_smul_left, ribbonIntersection_smul_left,
    ribbonIntersection_vertical_eq_displacement, ribbonIntersection_horizontal_eq_displacement] at he
  have hm := congrArg (fun z : ℚ => L * z) he
  have hx : L * (Y / L * diamondHorizontalDisplacement g.val) =
      Y * diamondHorizontalDisplacement g.val := by field_simp
  have hy : L * (X / L * -diamondVerticalDisplacement g.val) =
      -(X * diamondVerticalDisplacement g.val) := by field_simp
  linarith

end PottsDiscontinuity.Torus
