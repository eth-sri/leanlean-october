import RequestProject.TopologicalSingular.SmallMathlibComparison
import RequestProject.OrderNerveRealizationStarAcyclic
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular SingularSubdivision

/-- Every positive-dimensional singular cycle is homologous to one whose
individual simplices each lie in an open vertex star. -/
theorem orderNerveRealization_exists_small_cycle P [PartialOrder P]
    n c (hc : boundary n c = 0) :
    ∃ d,
      d ∈ smallChains (orderNerveRealizationOpenStar P) (n + 1) ∧
      boundary n d = 0 ∧ d - c ∈ LinearMap.range (boundary (n + 1)) :=
  exists_small_cycle_representative _
    (orderNerveRealizationOpenStar_isOpen P) (orderNerveRealizationOpenStar_cover P) n c hc
