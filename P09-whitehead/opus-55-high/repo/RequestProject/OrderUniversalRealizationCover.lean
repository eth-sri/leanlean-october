import RequestProject.OrderNerveRealizationRegular
import RequestProject.OrderUniversalPosetCover
import RequestProject.OrderUniversalDeck
import RequestProject.OrderUniversalPosetCells
import RequestProject.Tac


/-! Genuine regular topological covers from the constructed path-class order cover. -/

bwd

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
