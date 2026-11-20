module

public import PottsDiscontinuity.Torus.RibbonIntersection

/-!
# Bilinearity of the cyclic-order intersection pairing

The normalized primitive is given by explicit linear combinations of corner flows.
Consequently the induced edge coefficient and the intersection pairing are linear.
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

variable (hN : Even N) (hM : Even M) (A : RCConfig N M) (f g : diamondCycleSpace hN hM A)
    (d : DirectedDart (checkerArrows N M)) (c : ℚ)

theorem extendDiamondChain_add (f g : OpenDiamondEdge A → ℚ)
    (v : Fin N × Fin M) :
    extendDiamondChain (f + g) v = extendDiamondChain f v + extendDiamondChain g v := by
  by_cases hv : A v = true
  · simp [extendDiamondChain, hv, dite_true, Pi.add_apply]
  · simp [extendDiamondChain, hv, Bool.false_eq_true, dite_false, add_zero]

theorem extendDiamondChain_smul (f : OpenDiamondEdge A → ℚ)
    (c : ℚ) (v : Fin N × Fin M) :
    extendDiamondChain (c • f) v = c * extendDiamondChain f v := by
  by_cases hv : A v = true
  · simp [extendDiamondChain, hv, dite_true, Pi.smul_apply, smul_eq_mul]
  · simp [extendDiamondChain, hv, Bool.false_eq_true, dite_false, mul_zero]

theorem ribbonHalfFlow_add
    (f g : OpenDiamondEdge A → ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM (f + g) d =
      ribbonHalfFlow hN hM f d + ribbonHalfFlow hN hM g d := by
  simp only [ribbonHalfFlow, extendDiamondChain_add]
  grind

theorem ribbonHalfFlow_smul
    (f : OpenDiamondEdge A → ℚ) (c : ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM (c • f) d = c * ribbonHalfFlow hN hM f d := by
  simp [ribbonHalfFlow, extendDiamondChain_smul]

theorem ribbonCornerPrimitive_add :
    ribbonCornerPrimitive (f + g) d =
      ribbonCornerPrimitive f d + ribbonCornerPrimitive g d := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  simp only [ribbonCornerPrimitive_corner, Submodule.coe_add, ribbonHalfFlow_add]
  cases p <;> simp only [cornerPrimitiveValue] <;> ring

theorem ribbonCornerPrimitive_smul
    (f : diamondCycleSpace hN hM A) (c : ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive (c • f) d = c * ribbonCornerPrimitive f d := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  simp only [ribbonCornerPrimitive_corner, Submodule.coe_smul, ribbonHalfFlow_smul]
  cases p <;> simp only [cornerPrimitiveValue] <;> ring

theorem ribbonIntersectionCoefficient_add (e : OpenDiamondEdge A) :
    ribbonIntersectionCoefficient (f + g) e =
      ribbonIntersectionCoefficient f e + ribbonIntersectionCoefficient g e := by
  simp only [ribbonIntersectionCoefficient, ribbonCornerPrimitive_add, Submodule.coe_add, Pi.add_apply]
  ring

theorem ribbonIntersectionCoefficient_smul
    (f : diamondCycleSpace hN hM A) (c : ℚ) (e : OpenDiamondEdge A) :
    ribbonIntersectionCoefficient (c • f) e =
      c * ribbonIntersectionCoefficient f e := by
  simp only [ribbonIntersectionCoefficient, ribbonCornerPrimitive_smul,
    Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem ribbonIntersection_add_left
    (f g h : diamondCycleSpace hN hM A) :
    ribbonIntersection (f + g) h =
      ribbonIntersection f h + ribbonIntersection g h := by
  simp [ribbonIntersection, ribbonIntersectionCoefficient_add, add_mul, Finset.sum_add_distrib]

theorem ribbonIntersection_add_right
    (f g h : diamondCycleSpace hN hM A) :
    ribbonIntersection f (g + h) =
      ribbonIntersection f g + ribbonIntersection f h := by
  simp [ribbonIntersection, Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ribbonIntersection_smul_left :
    ribbonIntersection (c • f) g = c * ribbonIntersection f g := by
  simp [ribbonIntersection, ribbonIntersectionCoefficient_smul, mul_assoc, Finset.mul_sum]

theorem ribbonIntersection_smul_right :
    ribbonIntersection f (c • g) = c * ribbonIntersection f g := by
  simp only [ribbonIntersection, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  grind

end PottsDiscontinuity.Torus
