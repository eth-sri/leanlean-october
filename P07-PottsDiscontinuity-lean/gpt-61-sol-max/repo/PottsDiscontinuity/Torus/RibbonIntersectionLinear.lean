module
public import Mathlib

public import PottsDiscontinuity.Torus.RibbonIntersection

/-!
# Bilinearity of the cyclic-order intersection pairing

The normalized primitive is given by explicit linear combinations of corner flows.
Consequently the induced edge coefficient and the intersection pairing are linear.
-/

@[expose] public section



namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

theorem extendDiamondChain_add (A : RCConfig N M) (f g : OpenDiamondEdge A → ℚ)
    (v : Fin N × Fin M) :
    extendDiamondChain A (f + g) v = extendDiamondChain A f v + extendDiamondChain A g v := by
  by_cases hv : A v = true
  all_goals simp_all

theorem extendDiamondChain_smul (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ)
    (c : ℚ) (v : Fin N × Fin M) :
    extendDiamondChain A (c • f) v = c * extendDiamondChain A f v := by
  simp_all [extendDiamondChain]

section

variable (hN : Even N) (hM : Even M) (A : RCConfig N M)


theorem ribbonHalfFlow_add 
    (f g : OpenDiamondEdge A → ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM A (f + g) d =
      ribbonHalfFlow hN hM A f d + ribbonHalfFlow hN hM A g d := by
  simp only [ribbonHalfFlow, extendDiamondChain_add]
  split <;> ring

theorem ribbonHalfFlow_smul 
    (f : OpenDiamondEdge A → ℚ) (c : ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonHalfFlow hN hM A (c • f) d = c * ribbonHalfFlow hN hM A f d := by
  simp_all [ribbonHalfFlow, extendDiamondChain_smul]

theorem ribbonCornerPrimitive_add 
    (f g : diamondCycleSpace hN hM A) (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM A (f + g) d =
      ribbonCornerPrimitive hN hM A f d + ribbonCornerPrimitive hN hM A g d := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  simp only [ribbonCornerPrimitive_corner, Submodule.coe_add, ribbonHalfFlow_add]
  cases p <;> simp only [cornerPrimitiveValue] <;> ring

theorem ribbonCornerPrimitive_smul 
    (f : diamondCycleSpace hN hM A) (c : ℚ) (d : DirectedDart (checkerArrows N M)) :
    ribbonCornerPrimitive hN hM A (c • f) d = c * ribbonCornerPrimitive hN hM A f d := by
  obtain ⟨⟨v, p⟩, rfl⟩ := (ribbonCornerEquiv hN hM).surjective d
  simp only [ribbonCornerPrimitive_corner, Submodule.coe_smul, ribbonHalfFlow_smul]
  cases p <;> simp only [cornerPrimitiveValue] <;> ring

theorem ribbonIntersectionCoefficient_add 
    (f g : diamondCycleSpace hN hM A) (e : OpenDiamondEdge A) :
    ribbonIntersectionCoefficient hN hM A (f + g) e =
      ribbonIntersectionCoefficient hN hM A f e + ribbonIntersectionCoefficient hN hM A g e := by
  simp only [ribbonIntersectionCoefficient, ribbonCornerPrimitive_add, Submodule.coe_add, Pi.add_apply]
  ring

theorem ribbonIntersectionCoefficient_smul 
    (f : diamondCycleSpace hN hM A) (c : ℚ) (e : OpenDiamondEdge A) :
    ribbonIntersectionCoefficient hN hM A (c • f) e =
      c * ribbonIntersectionCoefficient hN hM A f e := by
  simp only [ribbonIntersectionCoefficient, ribbonCornerPrimitive_smul, Submodule.coe_smul, Pi.smul_apply]
  ring

theorem ribbonIntersection_add_left 
    (f g h : diamondCycleSpace hN hM A) :
    ribbonIntersection hN hM A (f + g) h =
      ribbonIntersection hN hM A f h + ribbonIntersection hN hM A g h := by
  simp only [ribbonIntersection, ribbonIntersectionCoefficient_add, add_mul, Finset.sum_add_distrib]

theorem ribbonIntersection_add_right 
    (f g h : diamondCycleSpace hN hM A) :
    ribbonIntersection hN hM A f (g + h) =
      ribbonIntersection hN hM A f g + ribbonIntersection hN hM A f h := by
  simp only [ribbonIntersection, Submodule.coe_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem ribbonIntersection_smul_left 
    (f g : diamondCycleSpace hN hM A) (c : ℚ) :
    ribbonIntersection hN hM A (c • f) g = c * ribbonIntersection hN hM A f g := by
  simp only [ribbonIntersection, ribbonIntersectionCoefficient_smul, mul_assoc, Finset.mul_sum]

theorem ribbonIntersection_smul_right 
    (f g : diamondCycleSpace hN hM A) (c : ℚ) :
    ribbonIntersection hN hM A f (c • g) = c * ribbonIntersection hN hM A f g := by
  simp only [ribbonIntersection, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  grind

end

end PottsDiscontinuity.Torus
