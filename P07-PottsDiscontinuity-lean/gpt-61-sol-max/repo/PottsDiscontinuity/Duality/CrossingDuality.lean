/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Probability statements use independent p and its true dual parameter. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.FiniteDuality
public import PottsDiscontinuity.Duality.RectangleDualCrossing
public import PottsDiscontinuity.Duality.RectangleCrossingExclusion

@[expose] public section

namespace PottsDiscontinuity.FK


noncomputable section


def rectangleDualBottomTopCrossingEvent (a : LatticeVertex) (w h : ℕ)  :=
  {A | ∃ b ∈ rectangleDualBottomPorts a w h,
    ∃ t ∈ rectangleDualTopPorts a w h,
      ActualConnected (rectangleDualGraph a w h) A b t}

section

variable (a : LatticeVertex) (w h : ℕ)


theorem rectangleHorizontalNoncrossing_subset_dualBottomTopCrossing_preimage
     :
    (rectangleHorizontalCrossingEvent a w h)ᶜ ⊆
       rectanglePrimalDualConfigurationEquiv a w h  ⁻¹'
        rectangleDualBottomTopCrossingEvent a w h := fun A hA => rectangleDualBottomTop_of_no_primal_horizontal_crossing a w h A hA 

/-- The true dual bottom/top port event is exactly the complement of the
actual primal horizontal crossing event under the finite primal-dual map. -/
theorem rectangleHorizontalComplement_eq_dualBottomTop_preimage
     :
    (rectangleHorizontalCrossingEvent a w h)ᶜ =
       rectanglePrimalDualConfigurationEquiv a w h  ⁻¹'
        rectangleDualBottomTopCrossingEvent a w h := by
  apply Set.ext
  intro A
  constructor
  · grind [rectangleHorizontalNoncrossing_subset_dualBottomTopCrossing_preimage]
  · intro hdual
    
    rcases hdual with ⟨b, hb, t, ht, hconn⟩
    
    
    
    
    
    
    intro hprimal
    exact rectanglePrimalDualCrossings_exclusive a w h A hprimal  ⟨b, t,  by
                                                                              rcases Finset.mem_image.mp hb with ⟨i, hi, rfl⟩
                                                                              rfl ,  by
                                                                                     rcases Finset.mem_image.mp ht with ⟨i, hi, rfl⟩
                                                                                     rfl , hconn⟩ 

/-- Exactly one of the actual primal and complementary-dual crossings occurs. -/
theorem rectangle_crossing_duality 
    (A : Configuration (rectangleGraph a w h)) :
    A ∉ rectangleHorizontalCrossingEvent a w h ↔
      rectanglePrimalDualConfigurationEquiv a w h A ∈
        rectangleDualBottomTopCrossingEvent a w h := by
  change A ∈ (rectangleHorizontalCrossingEvent a w h)ᶜ ↔ _
  rw [rectangleHorizontalComplement_eq_dualBottomTop_preimage]
  rfl

end

end
end PottsDiscontinuity.FK
