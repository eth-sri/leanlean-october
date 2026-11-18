module

public import RequestProject.OrderNerveRealizationRegular
public import RequestProject.OrderUniversalPosetCover
public import RequestProject.OrderUniversalDeck
public import RequestProject.OrderUniversalPosetCells

@[expose] public section

/-! Genuine regular topological covers from the constructed path-class order cover. -/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open Topology

variable {P : Type} [PartialOrder P] (a : P)

/-- The actual endpoint projection on geometric realizations. -/
noncomputable def uOrderRealizationProjection :
    C(orderNerveRealization (UOrder P a), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap uOrderEnd uOrderEnd_monotone,
    (orderNerveRealizationMap uOrderEnd uOrderEnd_monotone).hom.continuous⟩

theorem uOrderRealizationProjection_isCoveringMap (hc : IsConnected (orderCx P)) :
    IsCoveringMap (uOrderRealizationProjection a) :=
  (uOrderEnd_isPosetCover (a := a) hc).realizationMap_isCoveringMap

theorem uOrderRealizationProjection_surjective (hc : IsConnected (orderCx P)) :
    Function.Surjective (uOrderRealizationProjection a) :=
  (uOrderEnd_isPosetCover (a := a) hc).realizationMap_surjective

end FiniteChains.Comb
