module

public import RequestProject.PresUniversalRelatorMidpointReading
public import RequestProject.PresCoverCylinderRelatorBoundary

@[expose] public section

namespace FiniteChains.PresModel
open Comb
universe u v
variable {α J : Type u} {G : Type v} [Group G]
  (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)
  (gen : α → G) (hrel : ∀ j, wordVal gen (w j) = 1)

/-- The actual collapse in the universal presentation cover preserves actual vertex reading. -/
theorem presUniversalCylinderCollapse_reading
    (p : {p : UOrder _ (ptBase w) //
      uOrderEnd p ∈ coneAdjBaseSet}) :
    (presCoc w gen hrel).readVertex _
      (presCoverCylinderCollapse w uOrderEnd (presUniversalEnd_isPosetCover w hpos) p).val =
        (presCoc w gen hrel).readVertex _ p.val := by
  let f := uOrderEnd (a := ptBase w)
  let hf := presUniversalEnd_isPosetCover w hpos
  let q := presCoverCylinderCollapse w f hf p
  have hle :=
    (coneAdjCoverBaseEnd_isPosetCover f hf).le_upTransform
      _ (le_cylIn_cylRetr (aHom w)) p
  rw [(presCoc w gen hrel).readVertex_of_le _ p.val q.val hle]
  change (presCoc w gen hrel).readVertex _ p.val *
    (presCoc w gen hrel).val (f p.val) (f q.val) = _
  rw [← coneAdjCoverBaseEnd_spec f p, ← coneAdjCoverBaseEnd_spec f q]
  have hq : coneAdjCoverBaseEnd f q = cylCollapse _ (coneAdjCoverBaseEnd f p) :=
    cylinderCoverCollapse_projection w _ p; rw [hq]; change (presCoc w gen hrel).readVertex _ p.val *
    roseVal gen _
      (cylRetr (aHom w) (coneAdjCoverBaseEnd f p)) = _; rw [roseVal_self, mul_one]

/-- The actual collapsed lifted-relator midpoint has the same signed prefix reading. -/
theorem presUniversalRelator_collapsed_midpoint_reading
    (p : PresCoverRelator w _)
    (k : Fin _) :
    (presCoc w gen hrel).readVertex _
      (presCoverCylinderCollapse (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
        (presUniversalEnd_isPosetCover w hpos)
        (presCoverCircleCylinderInclusion (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
          (presUniversalEnd_isPosetCover w hpos) p
          (relatorCirclePoint w p.val.2 k CPos.cmid))).val =
      (presCoc w gen hrel).readVertex _ p.val.1 *
        (prefixVal w gen p.val.2 k.val *
          (if ((w p.val.2)[k.val]).2 then 1 else (gen ((w p.val.2)[k.val]).1)⁻¹)) := by
  rw [presUniversalCylinderCollapse_reading w hpos gen hrel]
  apply presUniversalRelator_midpoint_reading <;> assumption

end FiniteChains.PresModel
