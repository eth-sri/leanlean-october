/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.RectangleDualPotential

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

/-- The actual finite dual configuration is the open complement of the primal
configuration, transported across the true labelled-edge/graph-edge bijection. -/
noncomputable def rectangleDualConfigurationEquiv (a : LatticeVertex) (w h : ℕ) :
    Finset (rectanglePrimalEdgeCarrier a w h) ≃ Configuration (rectangleDualGraph a w h) := (rectangleDualComplementEquiv a w h).trans
                                                                                        (Equiv.finsetCongr (rectangleDualGraphEdgeEquiv a w h))

section

variable (a : LatticeVertex) (w h : ℕ)
include a w h

section

variable (A : Finset (rectanglePrimalEdgeCarrier a w h))


@[simp] theorem rectangleDualConfigurationEquiv_apply 
     :
    rectangleDualConfigurationEquiv a w h A = rectangleDualConfiguration a w h A := rfl

@[simp] theorem rectangleDualConfigurationEquiv_card 
     :
    (rectangleDualConfigurationEquiv a w h A).card =
      (rectangleDualComplementEquiv a w h A).card := by
  simp_all [rectangleDualConfigurationEquiv]

theorem rectangleDualConfiguration_card_add 
     :
    A.card + (rectangleDualConfigurationEquiv a w h A).card =
      Nat.card (rectangleDualGraph a w h).edgeSet := Eq.mpr
                                                       (congrArg (fun _a => A.card + _a = Nat.card ↑(rectangleDualGraph a w h).edgeSet)
                                                         (rectangleDualConfigurationEquiv_card a w h A))
                                                       (Trans.trans (rectangleDualComplement_card_add a w h A)
                                                         (Trans.trans (Eq.symm Nat.card_eq_fintype_card)
                                                           (Eq.symm
                                                             (Nat.card_congr ((rectangleDualGraphEdgeEquiv a w h).symm.trans (rectanglePrimalDualEdgeEquiv a w h).symm)))))

end
  

theorem rectangleDualGraph_edgeSet_card_eq_primal_edgeSet  :
    Nat.card (rectangleDualGraph a w h).edgeSet =
      Nat.card (rectangleGraph a w h).edgeSet := Nat.card_congr ((rectangleDualGraphEdgeEquiv a w h).symm.trans (rectanglePrimalDualEdgeEquiv a w h).symm)

theorem rectangleDualConfiguration_card_add_eq_primal_edgeSet
    
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    A.card + (rectangleDualConfiguration a w h A).card =
      Nat.card (rectangleGraph a w h).edgeSet := by
  grind [rectangleDualConfigurationEquiv_apply, rectangleDualConfiguration_card_add,
    rectangleDualGraph_edgeSet_card_eq_primal_edgeSet]

end

end PottsDiscontinuity.FK
