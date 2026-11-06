import Mathlib.Tactic

import RequestProject.TopologicalSingular.SmallMathlibComparison
import RequestProject.OrderNerveRealizationStarAcyclic

set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular SingularSubdivision

/-- Every positive-dimensional singular cycle is homologous to one whose
individual simplices each lie in an open vertex star. -/
abbrev orderNerveRealization_exists_small_cycle (P : Type) [PartialOrder P]
    (n : ℕ) (c : Chain (orderNerveRealization P) (n + 1)) (hc : boundary n c = 0)  :=
  FiniteChains.SingularSubdivision.exists_small_cycle_representative (FiniteChains.Comb.orderNerveRealizationOpenStar P)
    (FiniteChains.Comb.orderNerveRealizationOpenStar_isOpen P) (FiniteChains.Comb.orderNerveRealizationOpenStar_cover P) n
    c hc

end FiniteChains.Comb
