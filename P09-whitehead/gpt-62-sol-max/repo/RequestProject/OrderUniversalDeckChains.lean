module

public import RequestProject.StrictOrderNormalizationMaps
public import RequestProject.OrderUniversalPosetConnected
public import RequestProject.OrderComplexExt
public import RequestProject.ComponentComplex
public import RequestProject.DeckChainTransport
public import RequestProject.StrictOrderChains
public import RequestProject.OrderUniversalDeck

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
universe u
variable {P : Type u} [PartialOrder P] {a : P}

/-- In lifted order coordinates the deck action is the induced order map. -/
theorem uOrderHomInv_deck_square (g : Pi1 (orderCx P) a) :
    uOrderHomInv.comp ((univDeck (orderCx P) a).cellHom g) =
      (orderCxMap (uOrderDeck g) (uOrderDeckOrderIso g).monotone).comp uOrderHomInv := by
  apply Hom.ext_orderCx
  funext v
  change uOrderHomInv.onV (uOrderDeck g v) = uOrderDeck g (uOrderHomInv.onV v)
  rw [uOrderHomInv_vertex, uOrderHomInv_vertex]

theorem uOrderHom_deck_square (g : Pi1 (orderCx P) a) :
    uOrderHom.comp (orderCxMap (uOrderDeck g) (uOrderDeckOrderIso g).monotone) =
      ((univDeck (orderCx P) a).cellHom g).comp uOrderHom := by
  exact Hom.ext_uCover_orderCx rfl

end FiniteChains.Comb
