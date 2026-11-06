module

public import RequestProject.TopologicalSingular.SmallChainComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import RequestProject.TopologicalSingular.MathlibComparison
public import RequestProject.OrderNerveRealizationStarContractible

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology TopologicalSingular SingularSubdivision

/-- Every positive-dimensional singular cycle is homologous to one whose
individual simplices each lie in an open vertex star. -/
theorem orderNerveRealization_exists_small_cycle (P : Type) [PartialOrder P]
    (n : ℕ) (c : Chain (orderNerveRealization P) (n + 1)) (hc : boundary n c = 0) :
    ∃ d : Chain (orderNerveRealization P) (n + 1),
      d ∈ smallChains (orderNerveRealizationOpenStar P) (n + 1) ∧
      boundary n d = 0 ∧ d - c ∈ LinearMap.range (boundary (n + 1)) :=
  exists_small_cycle_representative (orderNerveRealizationOpenStar P)
    (orderNerveRealizationOpenStar_isOpen P) (orderNerveRealizationOpenStar_cover P) n c hc
