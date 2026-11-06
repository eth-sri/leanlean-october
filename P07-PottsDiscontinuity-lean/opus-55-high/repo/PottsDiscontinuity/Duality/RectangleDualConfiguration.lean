/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.RectangleDualPotential

@[expose] public section

namespace PottsDiscontinuity.FK

open PottsDiscontinuity.FK PottsDiscontinuity.FK.Medial

section
variable (a : LatticeVertex) (w h : ℕ)
/-- The actual finite dual configuration is the open complement of the primal
configuration, transported across the true labelled-edge/graph-edge bijection. -/
noncomputable def rectangleDualConfigurationEquiv  :
    Finset (rectanglePrimalEdgeCarrier a w h) ≃ Configuration (rectangleDualGraph a w h) :=
  (rectangleDualComplementEquiv a w h).trans
    (Equiv.finsetCongr (rectangleDualGraphEdgeEquiv a w h))

@[simp] theorem rectangleDualConfigurationEquiv_apply (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    rectangleDualConfigurationEquiv a w h A = rectangleDualConfiguration a w h A := by
  rfl

@[simp] theorem rectangleDualConfigurationEquiv_card (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    (rectangleDualConfigurationEquiv a w h A).card =
      (rectangleDualComplementEquiv a w h A).card := by
  simp [rectangleDualConfigurationEquiv]

theorem rectangleDualConfiguration_card_add (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    A.card + (rectangleDualConfigurationEquiv a w h A).card =
      Nat.card (rectangleDualGraph a w h).edgeSet := by
  rw [rectangleDualConfigurationEquiv_card]
  calc
    A.card + (rectangleDualComplementEquiv a w h A).card =
        Fintype.card (rectanglePrimalEdgeCarrier a w h) := (rectangleDualComplement_card_add a w h A)
    _ = Nat.card (rectangleDualGraph a w h).edgeSet := by
      calc
        Fintype.card (rectanglePrimalEdgeCarrier a w h) =
            Nat.card (rectanglePrimalEdgeCarrier a w h) := (Nat.card_eq_fintype_card (α := rectanglePrimalEdgeCarrier a w h)).symm
        _ = Nat.card (rectangleDualGraph a w h).edgeSet :=
          (Nat.card_congr ((rectangleDualGraphEdgeEquiv a w h).symm.trans
            (rectanglePrimalDualEdgeEquiv a w h).symm)).symm
  

theorem rectangleDualGraph_edgeSet_card_eq_primal_edgeSet  :
    Nat.card (rectangleDualGraph a w h).edgeSet =
      Nat.card (rectangleGraph a w h).edgeSet :=
  Nat.card_congr ((rectangleDualGraphEdgeEquiv a w h).symm.trans
    (rectanglePrimalDualEdgeEquiv a w h).symm)

theorem rectangleDualConfiguration_card_add_eq_primal_edgeSet
    (A : Finset (rectanglePrimalEdgeCarrier a w h)) :
    A.card + (rectangleDualConfiguration a w h A).card =
      Nat.card (rectangleGraph a w h).edgeSet := by
  grind [rectangleDualConfigurationEquiv_apply, rectangleDualConfiguration_card_add, rectangleDualGraph_edgeSet_card_eq_primal_edgeSet]
end

end PottsDiscontinuity.FK
