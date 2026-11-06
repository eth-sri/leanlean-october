import Mathlib.Tactic

import RequestProject.PresCoverRoseFibreEquiv
import RequestProject.PresUniversalGroupCoordinates
import RequestProject.PresUniversalRelatorDeck
import RequestProject.RoseCoverGeneratorEquiv

namespace FiniteChains.PresModel
open Comb
variable {α J : Type u} (ρ : J → FreeGroup α) (w : J → List (α × Bool))
  (hw : ∀ j, FreeGroup.mk (w j) = ρ j) (hpos : ∀ j, 0 < (w j).length)

/-- Reading coordinates on an actual universal rose-cover midpoint fibre. -/
noncomputable def presUniversalRoseMidpointFibreEquiv (i : α)  :=
  (presCoverRoseFibreEquiv w uOrderEnd (Rose.mid i)).trans
    (presUniversalFibreGroupEquiv ρ w hw hpos (iRose w (Rose.mid i)))

/-- Actual universal lifted midpoints are indexed by their reading and generator label. -/
noncomputable def presUniversalMidpointGroupEquiv :
    roseCoverMidpoints (cylinderCoverRoseEnd w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w)))) ≃ PresGroup ρ × α where
  toFun p := (presUniversalRoseMidpointFibreEquiv ρ w hw hpos p.val.2
    ⟨p.val.1, p.property⟩, p.val.2)
  invFun q :=
    let p := (presUniversalRoseMidpointFibreEquiv ρ w hw hpos q.2).symm q.1
    ⟨(p.val, q.2), p.property⟩
  left_inv p := by
    aesop
  right_inv q := by
    grind

/-- Selected actual universal rose edges have the same genuine group-generator coordinates. -/
noncomputable def presUniversalGeneratorGroupEquiv :
    roseCoverGeneratorEdges (cylinderCoverRoseEnd w
      (coneAdjCoverBaseEnd (uOrderEnd (P := PresPos w) (a := ptBase w))))
      (cylinderCoverRoseEnd_isPosetCover w _
        (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos))) ≃
      PresGroup ρ × α :=
  (roseCoverMidpointEdgeEquiv _
    (cylinderCoverRoseEnd_isPosetCover w _
      (coneAdjCoverBaseEnd_isPosetCover _ (presUniversalEnd_isPosetCover w hpos)))).symm.trans
    (presUniversalMidpointGroupEquiv ρ w hw hpos)

/-- Finite selected-edge coefficients in actual group-generator coordinates. -/
noncomputable def presUniversalGeneratorGroupChainEquiv  :=
  Finsupp.domLCongr (R := ℤ) (M := ℤ) (presUniversalGeneratorGroupEquiv ρ w hw hpos)

end FiniteChains.PresModel
