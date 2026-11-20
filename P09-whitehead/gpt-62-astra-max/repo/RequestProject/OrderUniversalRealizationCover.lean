module

public import RequestProject.OrderNerveRealizationRegular
public import RequestProject.OrderUniversalDeck
public import RequestProject.OrderUniversalPosetCells

@[expose] public section

/-! Genuine regular topological covers from the constructed path-class order cover. -/

namespace FiniteChains.Comb
open Topology

variable {P : Type} [PartialOrder P] (a : P)

/-- The actual endpoint projection on geometric realizations. -/
noncomputable def uOrderRealizationProjection :
    C(orderNerveRealization (UOrder P a), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap uOrderEnd uOrderEnd_monotone,
    (orderNerveRealizationMap uOrderEnd uOrderEnd_monotone).hom.continuous⟩

variable (hc : IsConnected (orderCx P))
include hc

theorem uOrderRealizationProjection_isCoveringMap :
    IsCoveringMap (uOrderRealizationProjection a) :=
  (uOrderEnd_isPosetCover hc).realizationMap_isCoveringMap

theorem uOrderRealizationProjection_surjective :
    Function.Surjective (uOrderRealizationProjection a) :=
  (uOrderEnd_isPosetCover hc).realizationMap_surjective

end FiniteChains.Comb
