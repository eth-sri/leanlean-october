module

public import RequestProject.PresUniversalGeneratorGroupCoordinates
public import RequestProject.PresCoverRelatorLetterCoefficients
public import RequestProject.PresUniversalCylinderCollapseReading

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- The actual lifted-letter midpoint coordinates are exactly the signed prefix coordinates. -/
theorem presUniversalLetter_midpoint_coordinates
    (p : PresCoverRelator w _)
    (k : Fin _) :
    presUniversalMidpointGroupEquiv ρ w hw hpos
      (presCoverRelatorLetterMidpoint (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
        (presUniversalEnd_isPosetCover w hpos) p k) =
      ((presGroupCocycle ρ w hw).readVertex _ p.val.1 *
        (prefixVal w (fun i => (QuotientGroup.mk (FreeGroup.of i)))
          p.val.2 k.val *
          (if ((w p.val.2)[k.val]).2 then 1 else
            (QuotientGroup.mk (FreeGroup.of ((w p.val.2)[k.val]).1))⁻¹)),
        ((w p.val.2)[k.val]).1) := by
  apply Prod.ext
  · apply presUniversalRelator_collapsed_midpoint_reading <;> assumption
  · rfl

/-- The selected incidence of an actual midpoint has that midpoint's group coordinates. -/
theorem presUniversalGeneratorGroupEquiv_midpoint
    (m : roseCoverMidpoints _) :
    presUniversalGeneratorGroupEquiv ρ w hw hpos
      (roseCoverMidpointEdge _ (cylinderCoverRoseEnd_isPosetCover w _
        (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos))) m) =
      presUniversalMidpointGroupEquiv ρ w hw hpos m := by
  change presUniversalMidpointGroupEquiv ρ w hw hpos
    ((roseCoverMidpointEdgeEquiv _ (cylinderCoverRoseEnd_isPosetCover w _
      (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos)))).symm
      ((roseCoverMidpointEdgeEquiv _ (cylinderCoverRoseEnd_isPosetCover w _
        (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos)))) m)) = _
  simp

end FiniteChains.PresModel
