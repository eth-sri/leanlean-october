import RequestProject.TopologicalPi1Lifting
import RequestProject.OrderRealizationHurewicz
import RequestProject.OrderUniversalRealizationCover
import RequestProject.Tac


bwd

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology

theorem orderH2Map_zero_of_orderNerveSingularH2Map_zero {P Q}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) hf
    (hz : (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)) = 0) : orderNerveH2Map f hf = 0 := by
  apply LinearMap.ext
  intro z
  apply (orderCellSingularH2Equiv Q).injective
  rw [← orderCellSingularH2Equiv_natural f hf, hz]
  exact (orderCellSingularH2Equiv Q).map_zero.symm
