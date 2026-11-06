import Mathlib.Tactic

import RequestProject.OrderNerveRealizationRegular
import RequestProject.OrderUniversalPosetCover
import RequestProject.OrderUniversalDeck
import RequestProject.OrderUniversalPosetCells

/-! Genuine regular topological covers from the constructed path-class order cover. -/

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb


variable {P : Type} [PartialOrder P] (a : P)

/-- The actual endpoint projection on geometric realizations. -/
noncomputable def uOrderRealizationProjection :
    C(orderNerveRealization (UOrder P a), orderNerveRealization P) :=
  ⟨orderNerveRealizationMap uOrderEnd uOrderEnd_monotone,
    (orderNerveRealizationMap uOrderEnd uOrderEnd_monotone).hom.continuous⟩

variable (hc : IsConnected (orderCx P))
include hc in
theorem uOrderRealizationProjection_isCoveringMap  :
    IsCoveringMap (uOrderRealizationProjection a) :=
  (uOrderEnd_isPosetCover (a := a) hc).realizationMap_isCoveringMap

include hc in
theorem uOrderRealizationProjection_surjective  :
    Function.Surjective (uOrderRealizationProjection a) :=
  (uOrderEnd_isPosetCover (a := a) hc).realizationMap_surjective

end FiniteChains.Comb
