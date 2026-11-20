module

public import RequestProject.StrictOrderNormalizationMaps
public import RequestProject.OrderUniversalPosetHom
public import RequestProject.OrderUniversalDeck

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- Actual lifted-order face coordinates commute with the actual path-class deck action. -/
theorem uOrderFace_deck (g : Pi1 (orderCx P) a) (t : OrdTri (UOrder P a)) :
    uOrderFace ((orderCxMap _ (uOrderDeckOrderIso g).monotone).onF t) =
      deckF g (uOrderFace t) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change (endV (deckV g t.1.1), endV (deckV g t.1.2.1), endV (deckV g t.1.2.2)) =
      (endV _, endV _, endV _)
    simp

end FiniteChains.Comb
