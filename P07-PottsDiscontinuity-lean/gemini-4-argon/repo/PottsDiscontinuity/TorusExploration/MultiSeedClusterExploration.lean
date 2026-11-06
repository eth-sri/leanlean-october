/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: import/namespace relocation; existing FK.Parameters replaces ClusterWeight, permitting all q >= 1 and 0 < p < 1. -/
module

public import PottsDiscontinuity.FK.ConditionalEmbeddedLaw
public import PottsDiscontinuity.TorusExploration.AdaptiveDomainMarkov
public import PottsDiscontinuity.TorusExploration.ClusterExploration

@[expose] public section

namespace PottsDiscontinuity.FK

noncomputable section

variable {V : Type*} [Finite V] {G : SimpleGraph V}

local instance multiSeedClusterEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance multiSeedClusterEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- A vertex belongs to the union of the actual open clusters rooted at `S`. -/
def actualMultiClusterConnected (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G) (u : V) : Prop :=
  ∃ s, s ∈ S ∧ ActualConnected G A s u

/-- All edges incident to any actual open cluster rooted at a seed in `S`. -/
def actualMultiClusterReveal (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G) : Configuration G := by
  classical
  exact Finset.univ.filter fun e : G.edgeSet =>
    ∃ u : V, u ∈ e.1 ∧ actualMultiClusterConnected G S A u

theorem actualMultiClusterReveal_mem_iff (S : Finset V) (A : Configuration G)
    (e : G.edgeSet) :
    e ∈ actualMultiClusterReveal G S A ↔
      ∃ u : V, u ∈ e.1 ∧ ∃ s, s ∈ S ∧ ActualConnected G A s u := by
  classical rw [actualMultiClusterReveal, Finset.mem_filter_univ]; rfl

theorem actualClusterReveal_subset_multi (S : Finset V) (A : Configuration G)
    {s : V} (hs : s ∈ S) :
    actualClusterReveal G s A ⊆ actualMultiClusterReveal G S A := fun e he => by
  rcases (actualClusterReveal_mem_iff G s A e).mp he with ⟨u, hu, hconn⟩
  exact (actualMultiClusterReveal_mem_iff S A e).mpr ⟨u, hu, s, hs, hconn⟩

private theorem single_reveal_agreement_of_multi
    (S : Finset V) (A B : Configuration G)
    (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A)
    {s : V} (hs : s ∈ S) :
    B ∩ actualClusterReveal G s A = A ∩ actualClusterReveal G s A := by
  classical
  ext e
  have heq := Finset.ext_iff.mp hagree e
  simp only [Finset.mem_inter] at heq ⊢
  exact ⟨fun ⟨heB, heS⟩ => ⟨(heq.mp ⟨heB, actualClusterReveal_subset_multi S A hs heS⟩).1, heS⟩,
    fun ⟨heA, heS⟩ => ⟨(heq.mpr ⟨heA, actualClusterReveal_subset_multi S A hs heS⟩).1, heS⟩⟩

theorem actualMultiClusterConnected_iff_of_reveal_agreement
    (S : Finset V) (A B : Configuration G)
    (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A)
    (u : V) :
    actualMultiClusterConnected G S B u ↔ actualMultiClusterConnected G S A u :=
  exists_congr fun s => and_congr_right fun hs =>
    actualConnected_iff_of_reveal_agreement G s A B
      (single_reveal_agreement_of_multi S A B hagree hs) u

theorem actualMultiClusterReveal_consistent
    (S : Finset V) (A B : Configuration G)
    (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A) :
    actualMultiClusterReveal G S B = actualMultiClusterReveal G S A := by
  ext e
  rw [actualMultiClusterReveal_mem_iff, actualMultiClusterReveal_mem_iff]
  exact exists_congr fun u => and_congr_right fun _ =>
    actualMultiClusterConnected_iff_of_reveal_agreement S A B hagree u

def actualMultiClusterComplementSet (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G) : Set V :=
  {u | ¬ actualMultiClusterConnected G S A u}

def actualMultiClusterComplementEmbedding (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G) : actualMultiClusterComplementSet G S A ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem edgeRestriction_actualMultiClusterReveal_eq_induced_complement
    (S : Finset V) (A : Configuration G) :
    edgeRestriction G (actualMultiClusterReveal G S A) =
      (G.induce (actualMultiClusterComplementSet G S A)).map
        (actualMultiClusterComplementEmbedding G S A) := by
  ext x y
  rw [edgeRestriction, SimpleGraph.deleteEdges_adj, SimpleGraph.map_adj]
  refine ⟨fun ⟨hAdj, hNot⟩ => ?_, ?_⟩
  · refine ⟨⟨x, fun ⟨s, hs, hconn⟩ => hNot ?_⟩, ⟨y, fun ⟨s, hs, hconn⟩ => hNot ?_⟩, hAdj, rfl, rfl⟩
    · exact (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A) ⟨s(x, y), G.mem_edgeSet.mpr hAdj⟩).mpr
        ((actualMultiClusterReveal_mem_iff S A _).mpr ⟨x, Sym2.mem_mk_left _ _, s, hs, hconn⟩)
    · exact (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A) ⟨s(x, y), G.mem_edgeSet.mpr hAdj⟩).mpr
        ((actualMultiClusterReveal_mem_iff S A _).mpr ⟨y, Sym2.mem_mk_right _ _, s, hs, hconn⟩)
  · rintro ⟨u, w, hAdj, rfl, rfl⟩
    refine ⟨hAdj, fun hmem => ?_⟩
    rcases (actualMultiClusterReveal_mem_iff S A ⟨s(u.val, w.val), G.mem_edgeSet.mpr hAdj⟩).mp
      ((coe_mem_openEdges_iff G (actualMultiClusterReveal G S A) _).mp hmem) with ⟨z, hz, s, hs, hconn⟩
    rcases Sym2.mem_iff.mp hz with rfl | rfl
    · exact u.2 ⟨s, hs, hconn⟩
    · exact w.2 ⟨s, hs, hconn⟩

theorem actualMultiClusterComplementGraph_le
    (S : Finset V) (A : Configuration G) :
    (G.induce (actualMultiClusterComplementSet G S A)).map
      (actualMultiClusterComplementEmbedding G S A) ≤ G := by
  rw [← edgeRestriction_actualMultiClusterReveal_eq_induced_complement]
  exact edgeRestriction_le G (actualMultiClusterReveal G S A)

theorem actualMultiClusterReveal_eq_subgraphRemovedEdges
    (S : Finset V) (A : Configuration G) :
    actualMultiClusterReveal G S A =
      subgraphRemovedEdges
        ((G.induce (actualMultiClusterComplementSet G S A)).map
          (actualMultiClusterComplementEmbedding G S A)) G := by
  ext e
  rw [mem_subgraphRemovedEdges, ← edgeRestriction_actualMultiClusterReveal_eq_induced_complement]
  simp [edgeRestriction_edgeSet, e.property, coe_mem_openEdges_iff]

/-- Conditioning on the union of actual clusters rooted at a finite seed set
leaves the exact FK law on the induced complement graph. -/
theorem law_filter_actualMultiClusterRecord_map_complement
    (q : Parameters) (ξ : BoundaryCondition V) (S : Finset V)
    (A₀ : Configuration G) :
    ((law G q ξ).filter
      (revealRecordEvent G (actualMultiClusterReveal G S) A₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent G (actualMultiClusterReveal G S)
          (actualMultiClusterReveal_consistent S) A₀]
        exact frozenStateEvent_support q ξ (actualMultiClusterReveal G S A₀)
          (revealRecordConfiguration G (actualMultiClusterReveal G S) A₀))).map
        (embeddedConfigurationRestriction
          (G.induce (actualMultiClusterComplementSet G S A₀)) G
          (actualMultiClusterComplementEmbedding G S A₀)
          (actualMultiClusterComplementGraph_le (G := G) S A₀)) =
      law (G.induce (actualMultiClusterComplementSet G S A₀)) q
        (isolatedExtensionPullbackBoundary (actualMultiClusterComplementEmbedding G S A₀)
          (frozenBoundary ξ
            (revealRecordConfiguration G (actualMultiClusterReveal G S) A₀).val)) := by
  let C := actualMultiClusterComplementSet G S A₀
  let f := actualMultiClusterComplementEmbedding G S A₀
  let H := (G.induce C).map f
  let R := actualMultiClusterReveal G S A₀
  let K := revealRecordConfiguration G (actualMultiClusterReveal G S) A₀
  have hR : R = subgraphRemovedEdges H G :=
    actualMultiClusterReveal_eq_subgraphRemovedEdges (G := G) S A₀
  let K' : RemovedConfiguration G (subgraphRemovedEdges H G) := ⟨K.val, hR ▸ K.property⟩
  have hHG : H ≤ G := actualMultiClusterComplementGraph_le (G := G) S A₀
  have hfiltered :
      (law G q ξ).filter (revealRecordEvent G (actualMultiClusterReveal G S) A₀)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent G (actualMultiClusterReveal G S)
            (actualMultiClusterReveal_consistent S) A₀]
          exact frozenStateEvent_support q ξ (actualMultiClusterReveal G S A₀)
            (revealRecordConfiguration G (actualMultiClusterReveal G S) A₀)) =
      (law G q ξ).filter (frozenStateEvent (subgraphRemovedEdges H G) K')
        (frozenStateEvent_support q ξ (subgraphRemovedEdges H G) K') := by
    ext C'
    have hEv : frozenStateEvent (actualMultiClusterReveal G S A₀) K =
        frozenStateEvent (subgraphRemovedEdges H G) K' := by
      ext A; simp [frozenStateEvent, K', K, R, hR]
    simp [PMF.filter_apply, revealRecordEvent_eq_frozenStateEvent G (actualMultiClusterReveal G S)
      (actualMultiClusterReveal_consistent S) A₀, K, hEv]
  simpa [H, f, K, R, C, K', isolatedExtensionPullbackBoundary, hR] using
    (congrArg (PMF.map (embeddedConfigurationRestriction (G.induce C) G f hHG)) hfiltered).trans
      (law_filter_frozen_map_embeddedRestriction (G.induce C) G f hHG q ξ K')

end
end PottsDiscontinuity.FK
