/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarFiniteCycleSupportedFlow
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceBoundaryDivergence
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleFilling

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial



 theorem parafermionicCoverSimpleCycleFilling_coefficient_orientation
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ∃ k : ℤ, (k = -1 ∨ k = 1) ∧
      ∀ d ∈ p.darts,
        parafermionicCoverFaceBoundaryCoefficient
          (parafermionicCoverSimpleCycleFillingSet hn p hp) d.fst d.snd = k := by
  
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let c  :=
    parafermionicCoverFaceBoundaryCoefficient S
  have hspec := parafermionicCoverSimpleCycleFillingSet_spec hn p hp
  
  
  
  
  
  simpa  using
     cycleSupportedFlow_constantOnDarts_sign
      (parafermionicCoverBoxGraph n) p hp c (parafermionicCoverFaceBoundaryCoefficient_antisymm S) (parafermionicCoverFaceBoundaryCoefficient_divergence S) (by
                                                              grind) (by
                                                                       grind) (by
                                                                                intro x y
                                                                                simpa  using parafermionicCoverFaceBoundaryCoefficient_mem S x y) 

end PottsDiscontinuity.TorusTopology.Planar.Medial
