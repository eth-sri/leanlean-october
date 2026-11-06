/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module
public import Mathlib

public import PottsDiscontinuity.FK.ConditionalLaw
public import PottsDiscontinuity.FK.IsolatedBoundaryLaw
public import PottsDiscontinuity.FK.SubgraphComparison

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
  (hGH : G.map f ≤ H)




local instance conditionalEmbeddedLawLargeEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _



/-- Conditioning on an exact state of all non-inner edges and restricting to
an embedded inner graph gives its FK law with every exterior induced
connection retained in the pulled-back boundary partition. -/
theorem law_filter_frozen_map_embeddedRestriction
    (q : Parameters) (ξ : BoundaryCondition W)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)) :
    ((law H q ξ).filter
      (frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
      (frozenStateEvent_support q ξ (subgraphRemovedEdges (G.map f) H) K)).map
        (embeddedConfigurationRestriction G H f hGH) =
      law G q
        (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) := by
  let R  := subgraphRemovedEdges (G.map f) H
  let B  := frozenBoundary ξ K.val
  let E  :=
    subgraphRemainingConfigurationEquiv hGH
  let split  :=
    fun C => (configurationSplitEquiv H R C).1
  let Q  :=
    (law H q ξ).filter (frozenStateEvent R K) (frozenStateEvent_support q ξ R K)
  have hfrozen := law_filter_frozen_map_remaining q ξ R K
  have hsub := law_subgraphRemaining_map hGH q B
  
  
  
  
  
  rw [← (by
           funext C
           dsimp [E]
           rw [subgraphRemainingConfigurationEquiv_symm_split]
           rfl : (fun C =>
      (isolatedExtensionConfigurationEquiv G f).symm (E.symm (split C))) =
      embeddedConfigurationRestriction G H f hGH)]
  simpa  using  by
                        calc
                          PMF.map (fun C => (isolatedExtensionConfigurationEquiv G f).symm
                              (E.symm (split C))) Q =
                            PMF.map ((isolatedExtensionConfigurationEquiv G f).symm ∘
                               fun C => E.symm (split C) ) Q := by
                            congr 1
                          _ = PMF.map (isolatedExtensionConfigurationEquiv G f).symm
                              (PMF.map (fun C => E.symm (split C)) Q) := by rw [PMF.map_comp]
                          _ = PMF.map (isolatedExtensionConfigurationEquiv G f).symm
                              (law (G.map f) q B) := congrArg _ (by
                                                                   calc
                                                                     PMF.map (fun C => E.symm (split C)) Q = PMF.map (E.symm ∘ split) Q := by
                                                                       congr 1
                                                                     _ = PMF.map E.symm (PMF.map split Q) := by rw [PMF.map_comp]
                                                                     _ = PMF.map E.symm (PMF.map E (law (G.map f) q B)) :=
                                                                       congrArg (PMF.map E.symm) (by
                                                                                                    aesop)
                                                                     _ = law (G.map f) q B := by
                                                                       rw [PMF.map_comp]
                                                                       simp only [Function.comp_def, Equiv.symm_apply_apply]
                                                                       exact PMF.map_id (law (G.map f) q B))
                          _ = law G q (isolatedExtensionPullbackBoundary f B) :=  by
                                                                                    
                                                                                    simpa [PMF.map_comp, PMF.map_id] using (congrArg
                                                                                                                              (fun μ : PMF (Configuration (G.map f)) =>
                                                                                                                                PMF.map (isolatedExtensionConfigurationEquiv G f).symm μ)
                                                                                                                              (law_isolatedExtension_map_boundary_pullback G f q B)).symm  

end
end PottsDiscontinuity.FK
