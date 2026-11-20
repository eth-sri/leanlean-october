/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Parameter generalization: independent 0 < p < 1 and 1 ≤ q, with no upper bound on q. -/
module

public import PottsDiscontinuity.FK.ConditionalLaw
public import PottsDiscontinuity.FK.EmbeddedMarginalLaw

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
  rw [map_embeddedConfigurationRestriction, law_filter_frozen_map_remaining,
    remainingLaw_map_embeddedRestriction]

end
end PottsDiscontinuity.FK
