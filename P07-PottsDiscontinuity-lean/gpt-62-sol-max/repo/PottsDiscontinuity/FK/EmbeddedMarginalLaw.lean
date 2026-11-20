/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.IsolatedBoundaryLaw
public import PottsDiscontinuity.FK.SubgraphComparison

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V W : Type*} [Finite V] [Finite W]
  (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W)
  (hGH : G.map f ≤ H)

local instance embeddedMarginalOuterEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

omit [Finite V] in
/-- Restriction to the embedded graph only reads retained edges. -/
theorem map_embeddedConfigurationRestriction (p : PMF (Configuration H)) :
    p.map (embeddedConfigurationRestriction G H f hGH) =
      (p.map (fun C => (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).1)).map
        (fun C => embeddedConfigurationRestriction G H f hGH C.val) := by
  rw [PMF.map_comp]
  congr 1
  funext C
  change _ = (isolatedExtensionConfigurationEquiv G f).symm
    ((subgraphRemainingConfigurationEquiv hGH).symm
      (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).1)
  rw [subgraphRemainingConfigurationEquiv_symm_split]
  rfl

theorem remainingLaw_map_embeddedRestriction (q : Parameters) (B : BoundaryCondition W) :
    (remainingLaw H q B (subgraphRemovedEdges (G.map f) H)).map
      (fun C => embeddedConfigurationRestriction G H f hGH C.val) =
      law G q (isolatedExtensionPullbackBoundary f B) := by
  let E := subgraphRemainingConfigurationEquiv hGH
  let I := isolatedExtensionConfigurationEquiv G f
  change (remainingLaw H q B _).map (I.symm ∘ E.symm) = _
  rw [← PMF.map_comp, ← law_subgraphRemaining_map hGH q B,
    ← law_isolatedExtension_map_boundary_pullback G f q B]
  have hc : I.symm ∘ E.symm ∘ E ∘ I = id := by ext x; simp
  simp only [PMF.map_comp]
  rw [hc, PMF.map_id]

/-- The true outer FK law, restricted to the embedded graph, is the mixture of
the exact inner FK laws induced by each actual removed-edge state. -/
theorem law_embeddedConfigurationRestriction_eq_bind_frozenMarginal
    (q : Parameters) (ξ : BoundaryCondition W) :
    (law H q ξ).map (embeddedConfigurationRestriction G H f hGH) =
      (frozenMarginalLaw q ξ (subgraphRemovedEdges (G.map f) H)).bind
        (fun K => law G q (isolatedExtensionPullbackBoundary f
          (frozenBoundary ξ K.val))) := by
  rw [map_embeddedConfigurationRestriction, law_map_remaining_eq_bind_frozen, PMF.map_bind]
  simp_rw [remainingLaw_map_embeddedRestriction]

end
end PottsDiscontinuity.FK
