import Mathlib.Tactic

import RequestProject.StrictOrderNormalizationMaps
import RequestProject.OrderUniversalChainNormalization
import RequestProject.OrderUniversalDeck

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
variable {P : Type u} [PartialOrder P] {a : P}

/-- Actual lifted-order face coordinates commute with the actual path-class deck action. -/
theorem uOrderFace_deck (g : Pi1 (orderCx P) a) (t : OrdTri (UOrder P a)) :
    uOrderFace ((orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onF t) =
      deckF g (uOrderFace t) := by
  apply_rules [Subtype.ext, Prod.ext, FiniteChains.Comb.endV_deckV]

end FiniteChains.Comb
