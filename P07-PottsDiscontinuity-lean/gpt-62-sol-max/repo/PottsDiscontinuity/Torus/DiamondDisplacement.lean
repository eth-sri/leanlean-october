module

public import PottsDiscontinuity.Torus.DiamondFullFlows

/-!
# Intersection coordinates are lifted displacement

With the endpoint-false to endpoint-true orientation, every primal edge has vertical
increment minus one; its horizontal increment is minus one at a black midpoint and
plus one at a white midpoint. 
-/

@[expose] public section

open Finset PottsDiscontinuity.SixVertex

namespace PottsDiscontinuity.Torus

variable {N M : ℕ}

/-- Horizontal displacement of an indexed primal chain in the integer-lattice lift. -/
def diamondHorizontalDisplacement (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ) : ℚ :=
  ∑ e, (if checker e.val then -1 else 1) * f e

/-- Vertical displacement of an indexed primal chain in the integer-lattice lift. -/
def diamondVerticalDisplacement (A : RCConfig N M) (f : OpenDiamondEdge A → ℚ) : ℚ :=
  -(∑ e, f e)

/-- The two displacement coordinates of a conserved chain. -/
def diamondDisplacementMap (hN : Even N) (hM : Even M) (A : RCConfig N M) :
    diamondCycleSpace hN hM A →ₗ[ℚ] ℚ × ℚ where
  toFun f := (diamondHorizontalDisplacement A f.val, diamondVerticalDisplacement A f.val)
  map_add' f g := by
    ext <;> simp [diamondHorizontalDisplacement, diamondVerticalDisplacement, mul_add, sum_add_distrib] <;> ring
  map_smul' c f := by
    ext <;> simp [diamondHorizontalDisplacement, diamondVerticalDisplacement, smul_eq_mul,
      Finset.mul_sum, mul_left_comm]

@[simp] theorem diamondDisplacementMap_apply (hN : Even N) (hM : Even M) (A : RCConfig N M)
    (f : diamondCycleSpace hN hM A) : diamondDisplacementMap hN hM A f =
      (diamondHorizontalDisplacement A f.val, diamondVerticalDisplacement A f.val) := rfl

end PottsDiscontinuity.Torus
