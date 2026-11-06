module

public import PottsDiscontinuity.Torus.DiamondFullFlows
public import PottsDiscontinuity.Torus.RibbonIntersectionAlternating

/-!
# Intersection coordinates are lifted displacement

With the endpoint-false to endpoint-true orientation, every primal edge has vertical
increment minus one; its horizontal increment is minus one at a black midpoint and
plus one at a white midpoint. The explicit full-torus flows recover these coordinates
through the cellular intersection pairing.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

section
variable (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
/-- Horizontal displacement of an indexed primal chain in the integer-lattice lift. -/
def diamondHorizontalDisplacement  : ℚ :=
  ∑ e, (if checker e.val then -1 else 1) * f e

/-- Vertical displacement of an indexed primal chain in the integer-lattice lift. -/
def diamondVerticalDisplacement  : ℚ :=
  -(∑ e, f e)
end

section
variable (hN : Even N) (hM : Even M)
theorem verticalDiamondCycle_primitive (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM (openRCConfig N M) (verticalDiamondCycle hN hM) d =
      cornerPrimitiveValue verticalCornerFlow d.val.2 := by
  rfl

theorem horizontalDiamondCycle_primitive (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM (openRCConfig N M) (horizontalDiamondCycle hN hM) d =
      cornerPrimitiveValue horizontalCornerFlow d.val.2 := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  simp
  change cornerPrimitiveValue (fun q => ribbonHalfFlow hN hM (openRCConfig N M)
    (horizontalDiamondFlow N M) (ribbonCornerEquiv hN hM (v, q))) p =
      cornerPrimitiveValue horizontalCornerFlow (faceCorner v.val p).2
  simp_rw [horizontalDiamondFlow_corner]
  cases p <;> rfl

theorem ribbonIntersectionCoefficient_vertical (e : OpenDiamondEdge (openRCConfig N M)) :
    ribbonIntersectionCoefficient hN hM (openRCConfig N M) (verticalDiamondCycle hN hM) e =
      if checker e.val then -1 else 1 := by
  unfold ribbonIntersectionCoefficient
  rw [verticalDiamondCycle_primitive, verticalDiamondCycle_primitive]
  simp only [ribbonEndEquiv_val, verticalDiamondCycle, verticalDiamondFlow]
  grind [checker, ribbonEnd, cornerPrimitiveValue, verticalCornerFlow]

theorem ribbonIntersectionCoefficient_horizontal (e : OpenDiamondEdge (openRCConfig N M)) :
    ribbonIntersectionCoefficient hN hM (openRCConfig N M) (horizontalDiamondCycle hN hM) e = 1 := by
  unfold ribbonIntersectionCoefficient
  rw [horizontalDiamondCycle_primitive, horizontalDiamondCycle_primitive]
  simp only [ribbonEndEquiv_val, horizontalDiamondCycle, horizontalDiamondFlow]
  grind [checker, ribbonEnd, cornerPrimitiveValue, horizontalCornerFlow]

theorem ribbonIntersection_vertical_eq_displacement (f : diamondCycleSpace hN hM (openRCConfig N M)) :
    ribbonIntersection hN hM (openRCConfig N M) (verticalDiamondCycle hN hM) f =
      diamondHorizontalDisplacement (openRCConfig N M) f.val := by
  simp [ribbonIntersection, ribbonIntersectionCoefficient_vertical, diamondHorizontalDisplacement]

theorem ribbonIntersection_horizontal_eq_displacement (f : diamondCycleSpace hN hM (openRCConfig N M)) :
    ribbonIntersection hN hM (openRCConfig N M) (horizontalDiamondCycle hN hM) f =
      -diamondVerticalDisplacement (openRCConfig N M) f.val := by
  simp [ribbonIntersection, ribbonIntersectionCoefficient_horizontal, diamondVerticalDisplacement]

theorem verticalDiamondCycle_displacement_x  :
    diamondHorizontalDisplacement (openRCConfig N M) (verticalDiamondCycle hN hM).val = 0 := by
  rw [← ribbonIntersection_vertical_eq_displacement, ribbonIntersection_self]

theorem verticalDiamondCycle_displacement_y  :
    diamondVerticalDisplacement (openRCConfig N M) (verticalDiamondCycle hN hM).val = -(N * M : ℚ) := by
  simp only [diamondVerticalDisplacement, verticalDiamondCycle, verticalDiamondFlow,
    Finset.sum_const, Finset.card_univ, card_openDiamondEdge, openCount_open,
    nsmul_eq_mul, mul_one, Nat.cast_mul]

theorem horizontalDiamondCycle_displacement_x  :
    diamondHorizontalDisplacement (openRCConfig N M) (horizontalDiamondCycle hN hM).val = -(N * M : ℚ) := by
  rw [← ribbonIntersection_vertical_eq_displacement, ribbonIntersection_antisymm,
    ribbonIntersection_horizontal_eq_displacement, neg_neg, verticalDiamondCycle_displacement_y]

theorem horizontalDiamondCycle_displacement_y  :
    diamondVerticalDisplacement (openRCConfig N M) (horizontalDiamondCycle hN hM).val = 0 := by
  have he := ribbonIntersection_self hN hM (openRCConfig N M) (horizontalDiamondCycle hN hM)
  simp_all [ribbonIntersection_horizontal_eq_displacement]
end

end PottsDiscontinuity.Torus
