import Mathlib.Tactic

import RequestProject.PresUniversalReadingPrefix
import RequestProject.PresUniversalRelatorDeck
import RequestProject.PresCoverRelatorFan

namespace FiniteChains.PresModel
open Comb
variable {α J : Type u} {G : Type v} [Group G]
  (w : J → List (α × Bool)) (hpos : ∀ j, 0 < (w j).length)
  (gen : α → G) (hrel : ∀ j, wordVal gen (w j) = 1)

/-- Reading the actual midpoint of an actual lifted relator gives its actual signed prefix. -/
theorem presUniversalRelator_midpoint_reading
    (p : PresCoverRelator w (uOrderEnd (P := PresPos w) (a := ptBase w)))
    (k : Fin (w p.val.2).length) :
    (presCoc w gen hrel).readVertex (ptBase w)
      (presCoverCircleInclusion (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd (presUniversalEnd_isPosetCover w hpos) p
        (relatorCirclePoint w p.val.2 k CPos.cmid)) =
      (presCoc w gen hrel).readVertex (ptBase w) p.val.1 *
        (prefixVal w gen p.val.2 k.val *
          (if ((w p.val.2)[k.val]).2 then 1 else (gen ((w p.val.2)[k.val]).1)⁻¹)) := by
  apply presUniversal_midpoint_reading w gen hrel (ptBase w) p.val.2 k.val _
    (List.getElem?_eq_getElem k.isLt)
  · exact (presCoverCircleInclusion_lt_apex (P := UOrder (PresPos w) (ptBase w)) w uOrderEnd
      (presUniversalEnd_isPosetCover w hpos) p _).le
  · solve_by_elim [FiniteChains.PresModel.presCoverConeCircleOrderIso_symm_projection]
  · exact p.property

end FiniteChains.PresModel
