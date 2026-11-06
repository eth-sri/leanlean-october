module

public import PottsDiscontinuity.TorusExploration.MultiSeedClusterExploration
public import PottsDiscontinuity.FK.BoundaryPartitionLaw

/-! Revealing complete clusters under a free outer law induces no identifications
between the remaining vertices. This is an actual conditional-law identity. -/

public section

namespace PottsDiscontinuity.FK
noncomputable section
variable {V : Type*} [Finite V] {G : SimpleGraph V}
local instance complementFreeEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

section
variable (S : Finset V) (A : Configuration G)
theorem no_revealed_open_edge_at_cluster_complement (u : actualMultiClusterComplementSet G S A) (w : V) :
    ¬ (openGraph G (A ∩ actualMultiClusterReveal G S A)).Adj u.val w := by
  intro hadj
  have hadjA := openGraph_mono (Finset.inter_subset_left (s₂ := actualMultiClusterReveal G S A)) hadj
  obtain ⟨e,he,hep⟩ := (openGraph_adj G (A ∩ actualMultiClusterReveal G S A) u.val w).mp hadj
  obtain ⟨z,hze,s,hs,hsz⟩ := (actualMultiClusterReveal_mem_iff S A e).mp ((Finset.mem_inter.mp he).2)
  rw [hep] at hze
  rcases Sym2.mem_iff'.mp hze with hzu | hzw
  · exact u.property ⟨s,hs,hzu ▸ hsz⟩
  · apply u.property
    refine ⟨s,hs,?_⟩
    subst z
    exact hsz.trans hadjA.symm.reachable

/-- The frozen record of complete clusters is free on their genuine complement. -/
theorem actualMultiClusterComplement_frozen_partition_free
     :
    (isolatedExtensionPullbackBoundary (actualMultiClusterComplementEmbedding G S A)
      (frozenBoundary (BoundaryCondition.free ∅)
        (revealRecordConfiguration G (actualMultiClusterReveal G S) A).val)).partition =
      (BoundaryCondition.free (∅ : Set (actualMultiClusterComplementSet G S A))).partition := by
  apply Setoid.ext
  intro u v
  change (componentSetoid G (BoundaryCondition.free ∅)
    (A ∩ actualMultiClusterReveal G S A)).r u.val v.val ↔ u=v
  rw [componentSetoid_free]
  constructor
  · rintro ⟨p⟩
    by_cases hp : p.Nil
    · grind
    · exact (no_revealed_open_edge_at_cluster_complement S A u _ (p.adj_snd hp)).elim
  simp_all
end

/-- Adaptive domain Markov with the induced boundary discharged: after revealing
the clusters of all seeds, the unobserved induced graph has exactly its free law. -/
theorem law_filter_actualMultiClusterRecord_map_complement_free
    (q : Parameters) (S : Finset V) (A : Configuration G) :
    ((law G q (BoundaryCondition.free ∅)).filter
      (revealRecordEvent G (actualMultiClusterReveal G S) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent G (actualMultiClusterReveal G S)
          (actualMultiClusterReveal_consistent S) A]
        exact frozenStateEvent_support q (BoundaryCondition.free ∅) (actualMultiClusterReveal G S A)
          (revealRecordConfiguration G (actualMultiClusterReveal G S) A))).map
        (embeddedConfigurationRestriction
          (G.induce (actualMultiClusterComplementSet G S A)) G
          (actualMultiClusterComplementEmbedding G S A)
          (actualMultiClusterComplementGraph_le S A)) =
      law (G.induce (actualMultiClusterComplementSet G S A)) q
        (BoundaryCondition.free ∅) := by
  rw [law_filter_actualMultiClusterRecord_map_complement]
  exact law_eq_of_boundary_partition_eq q _ _
    (actualMultiClusterComplement_frozen_partition_free S A)

end
end PottsDiscontinuity.FK
