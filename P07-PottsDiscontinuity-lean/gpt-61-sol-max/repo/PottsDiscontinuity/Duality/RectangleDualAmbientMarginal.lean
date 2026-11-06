/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.RectangleDualAmbient
public import PottsDiscontinuity.FK.SubgraphComparison

@[expose] public section

namespace PottsDiscontinuity.FK



noncomputable section

theorem rectangleDualAmbient_law_restrict_to_dual
    (a : LatticeVertex) (w h : ℕ) (q : Parameters) :
    (law (rectangleDualAmbientGraph a w h) q (rectangleDualBoundaryCondition a w h)).map
      (subgraphConfigurationRestriction (rectangleDualGraph_le_ambient a w h)) =
    law (rectangleDualGraph a w h) q (rectangleDualBoundaryCondition a w h) := by
  
  
  
  let H := rectangleDualAmbientGraph a w h
  let G := rectangleDualGraph a w h
  let hGH  := rectangleDualGraph_le_ambient a w h
  let rectangleDualAmbientEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _
  let R := subgraphRemovedEdges G H
  
  
  
  calc
    (law H q (rectangleDualBoundaryCondition a w h)).map
        (subgraphConfigurationRestriction hGH) =
      ((law H q (rectangleDualBoundaryCondition a w h)).map
         fun C => (configurationSplitEquiv H R C).1 ).map
           (subgraphRemainingConfigurationEquiv hGH).symm  := by
        rw [PMF.map_comp]
        congr 1
        funext C
        simpa only [Function.comp_apply] using
          (subgraphRemainingConfigurationEquiv_symm_split hGH C).symm
    _ = ((law G q (rectangleDualBoundaryCondition a w h)).map
        (subgraphRemainingConfigurationEquiv hGH)).map
          (subgraphRemainingConfigurationEquiv hGH).symm := by
        rw [(law_map_remove H q (rectangleDualBoundaryCondition a w h) R (by
                                                                                            intro u v huv he
                                                                                            
                                                                                            right
                                                                                            
                                                                                            exact rectangleDualAmbient_extraEdge_endpoints_boundary a w h u v huv (by
                                                                                                                                                                     aesop))),  law_subgraphRemaining_map hGH q (rectangleDualBoundaryCondition a w h) ]
    _ = law G q (rectangleDualBoundaryCondition a w h) := by
        rw [PMF.map_comp]
        have heq :  (subgraphRemainingConfigurationEquiv hGH).symm ∘
            subgraphRemainingConfigurationEquiv hGH  = id := Equiv.symm_comp_self (subgraphRemainingConfigurationEquiv hGH)
        rw [heq, PMF.map_id]

end

end PottsDiscontinuity.FK
