module

public import RequestProject.StrictOrderNormalizationMaps
public import RequestProject.OrderUniversalChainNormalization
public import RequestProject.OrderUniversalDeck

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Actual lifted-order face coordinates commute with the actual path-class deck action. -/
theorem uOrderFace_deck (g : Pi1 (orderCx P) a) (t : OrdTri (UOrder P a)) :
    uOrderFace ((orderCxMap (uOrderDeckOrderIso g) (uOrderDeckOrderIso g).monotone).onF t) =
      deckF g (uOrderFace t) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (endV (deckV g t.1.1), endV (deckV g t.1.2.1), endV (deckV g t.1.2.2)) =
      (endV t.1.1, endV t.1.2.1, endV t.1.2.2)
    simp only [endV_deckV]

end FiniteChains.Comb
