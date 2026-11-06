module

public import RequestProject.TopologicalSingular.HurewiczIsomorphismConsequences
public import Mathlib.Topology.Homotopy.Lifting
public import RequestProject.TopologicalSingular.HurewiczInjectivity
public import RequestProject.TopologicalSingular.TetrahedronGeneralFaceRelation
public import RequestProject.TopologicalSingular.CoherentSimplexExtension
public import RequestProject.TopologicalSingular.CoherentTriangleNormalization
public import RequestProject.TopologicalSingular.HurewiczSurjectivity
public import RequestProject.OrderNerveSingularH2Iso
public import RequestProject.OrderUniversalRealizationSimplyConnected
public import RequestProject.OrderUniversalRealizationCover

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Comb
open CategoryTheory AlgebraicTopology

theorem orderH2Map_zero_of_orderNerveSingularH2Map_zero {P Q : Type}
    [PartialOrder P] [PartialOrder Q] (f : P → Q) (hf : Monotone f)
    (hz : (((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).map
      (orderNerveRealizationMap f hf)) = 0) : orderNerveH2Map f hf = 0 := by
  apply LinearMap.ext
  intro z
  apply (orderCellSingularH2Equiv Q).injective
  rw [← orderCellSingularH2Equiv_natural f hf, hz]
  exact (orderCellSingularH2Equiv Q).map_zero.symm
