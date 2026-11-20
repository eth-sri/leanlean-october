module

public import PottsDiscontinuity.CorrLength.ConnectionEvents

/-! # Actual connectivity under closed extension and embedded restriction -/

@[expose] public section

namespace PottsDiscontinuity.TorusRC

open CorrLength FK

noncomputable section

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Mapping a finite edge configuration retains exactly its open graph. -/
theorem openGraph_map_embedding
    (f : G ↪g H) (A : Configuration G) :
    openGraph (A.map f.mapEdgeSet) = (openGraph A).map f.toEmbedding := by
  apply SimpleGraph.edgeSet_injective
  rw [openGraph_edgeSet,SimpleGraph.edgeSet_map,openGraph_edgeSet]
  simp [openEdges, Finset.coe_map, Set.image_image]

/-- The infinite-carrier finite-witness event under closed extension is
exactly connectivity by the sampled finite edge set. -/
theorem boxConfiguration_connection_iff (c : LatticeVertex) (r : ℕ)
    (A : Configuration (boxGraph c r)) (u v : BoxVertex c r) :
    boxConfiguration c r A ∈ connectionEvent u.val v.val ↔
      ActualConnected A u v := by
  classical
  have hw : boxConfiguration c r A ∈ connectionEvent u.val v.val ↔
      ActualConnected (A.map (boxEdgeEmbedding c r)) u.val v.val := by
    constructor
    · rintro ⟨F,hF,hopen⟩
      apply actualConnected_mono (fun e he => (boxConfiguration_open_iff c r A e).mp (hopen e he)) hF
    · intro h
      refine ⟨A.map (boxEdgeEmbedding c r),h,?_⟩
      intro e he
      exact (boxConfiguration_open_iff c r A e).mpr he
  rw [hw]
  change (openGraph (A.map (boxGraphEmbedding c r).mapEdgeSet)).Reachable
    ((boxGraphEmbedding c r).toEmbedding u) ((boxGraphEmbedding c r).toEmbedding v) ↔ _
  rw [openGraph_map_embedding,reachable_isolatedExtension_apply]
  rfl

/-- Connections in the exact embedded restriction remain actual connections
in the full sampled graph. No boundary identifications are used. -/
theorem actualConnected_embeddedRestriction (f : V ↪ W) (hGH : G.map f ≤ H)
    (A : Configuration H) (u v : V)
    (h : ActualConnected (embeddedConfigurationRestriction G H f hGH A) u v) :
    ActualConnected A (f u) (f v) := by
  let B := embeddedConfigurationRestriction G H f hGH A
  have hm :=
    (actualConnected_isolatedExtension G f B u v).mpr h
  have he : ActualConnected (embeddedConfigurationEmbedding G H f hGH B) (f u) (f v) := by
    change (openGraph (subgraphConfigurationEmbedding hGH
      (isolatedExtensionConfigurationEquiv G f B))).Reachable _ _
    rw [openGraph_subgraphConfigurationEmbedding]
    exact hm
  exact actualConnected_mono
    (embeddedConfigurationEmbedding_restriction_subset G H f hGH A) he

end
end PottsDiscontinuity.TorusRC
