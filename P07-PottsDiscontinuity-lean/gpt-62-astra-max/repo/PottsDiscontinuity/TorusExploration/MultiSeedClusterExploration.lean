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

variable {G : SimpleGraph V} (q : Parameters) (ξ : BoundaryCondition V) (S : Finset V)
    (A : Configuration G)

include S A in
/-- A vertex belongs to the union of the actual open clusters rooted at `S`. -/
def actualMultiClusterConnected (u : V) : Prop :=
  ∃ s, s ∈ S ∧ ActualConnected A s u

/-- All edges incident to any actual open cluster rooted at a seed in `S`. -/
def actualMultiClusterReveal (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G) : Configuration G := by
  classical
  exact Finset.univ.filter fun e : G.edgeSet =>
    ∃ u, u ∈ e.1 ∧ actualMultiClusterConnected S A u

theorem actualMultiClusterReveal_mem_iff
    (e : G.edgeSet) :
    e ∈ actualMultiClusterReveal G S A ↔
      ∃ u, u ∈ e.1 ∧ ∃ s, s ∈ S ∧ ActualConnected A s u := by
  classical
  change (e ∈ Finset.univ.filter fun e : G.edgeSet =>
    ∃ u, u ∈ e.1 ∧ actualMultiClusterConnected S A u) ↔ _
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Iff.rfl

theorem actualClusterReveal_subset_multi
    {s : V} (hs : s ∈ S) :
    actualClusterReveal G s A ⊆ actualMultiClusterReveal G S A := by
  intro e he
  rw [actualMultiClusterReveal_mem_iff]
  rcases (actualClusterReveal_mem_iff G s A e).mp he with ⟨u, hu, hconn⟩
  grind

private theorem single_reveal_agreement_of_multi
    {S : Finset V} {A B : Configuration G}
    (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A)
    {s : V} (hs : s ∈ S) :
    B ∩ actualClusterReveal G s A = A ∩ actualClusterReveal G s A := by
  classical
  apply Finset.ext
  intro e
  simp only [Finset.mem_inter]
  have heq := Finset.ext_iff.mp hagree e
  constructor
  · rintro ⟨heB, heSingle⟩
    have heMulti := actualClusterReveal_subset_multi S A hs heSingle
    grind
  · rintro ⟨heA, heSingle⟩
    have heMulti := actualClusterReveal_subset_multi S A hs heSingle
    grind

theorem actualMultiClusterConnected_iff_of_reveal_agreement (A B : Configuration G)
    (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A)
    (u : V) :
    actualMultiClusterConnected S B u ↔ actualMultiClusterConnected S A u := by
  constructor
  · rintro ⟨s, hs, hconn⟩
    exact ⟨s, hs, (actualConnected_iff_of_reveal_agreement G
      (single_reveal_agreement_of_multi hagree hs) u).mp hconn⟩
  · rintro ⟨s, hs, hconn⟩
    exact ⟨s, hs, (actualConnected_iff_of_reveal_agreement G
      (single_reveal_agreement_of_multi hagree hs) u).mpr hconn⟩

theorem actualMultiClusterReveal_consistent (A B : Configuration G)
    (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A) :
    actualMultiClusterReveal G S B = actualMultiClusterReveal G S A := by
  ext e
  rw [actualMultiClusterReveal_mem_iff, actualMultiClusterReveal_mem_iff]
  constructor
  · rintro ⟨u, hu, s, hs, hconn⟩
    exact ⟨u, hu, s, hs, (actualConnected_iff_of_reveal_agreement G
      (single_reveal_agreement_of_multi hagree hs) u).mp hconn⟩
  · rintro ⟨u, hu, s, hs, hconn⟩
    exact ⟨u, hu, s, hs, (actualConnected_iff_of_reveal_agreement G
      (single_reveal_agreement_of_multi hagree hs) u).mpr hconn⟩

include S A in
def actualMultiClusterComplementSet : Set V :=
  {u | ¬ actualMultiClusterConnected S A u}

def actualMultiClusterComplementEmbedding : actualMultiClusterComplementSet S A ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

theorem edgeRestriction_actualMultiClusterReveal_eq_induced_complement :
    edgeRestriction G (actualMultiClusterReveal G S A) =
      (G.induce (actualMultiClusterComplementSet S A)).map
        (actualMultiClusterComplementEmbedding S A) := by
  ext x y
  constructor
  · intro hxy
    rcases (by simpa [edgeRestriction] using hxy) with ⟨hAdj, hNot⟩
    let edges' := coe_mem_openEdges_iff G (actualMultiClusterReveal G S A) ⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩
    have hnotConn :
        ¬ actualMultiClusterConnected S A x ∧
        ¬ actualMultiClusterConnected S A y := by
      constructor
      · intro hx
        apply hNot
        rcases hx with ⟨s, hs, hconn⟩
        exact (edges').mpr (by grind [actualMultiClusterReveal_mem_iff])
      · intro hy
        apply hNot
        rcases hy with ⟨s, hs, hconn⟩
        exact (edges').mpr (by grind [actualMultiClusterReveal_mem_iff])
    apply (SimpleGraph.map_adj _
      _ x y).2
    refine ⟨⟨x, hnotConn.1⟩, ⟨y, hnotConn.2⟩, ?_, rfl, rfl⟩
    exact SimpleGraph.induce_adj.mpr hAdj
  · intro hxy
    rcases (SimpleGraph.map_adj _
      _ x y).1 hxy with
      ⟨u, w, hAdjInduced, hux, hwy⟩
    have hAdj := SimpleGraph.induce_adj.mp hAdjInduced
    subst x
    subst y
    rw [edgeRestriction, SimpleGraph.deleteEdges_adj]
    refine ⟨hAdj, ?_⟩
    intro hmem
    rcases (actualMultiClusterReveal_mem_iff S A _).mp (by
      apply (coe_mem_openEdges_iff G _
        ⟨s(u,w), G.mem_edgeSet.mpr hAdj⟩).mp
      assumption) with
      ⟨z, hz, s, hs, hconn⟩
    rcases Sym2.mem_iff'.mp hz with hzu | hzw
    · exact u.2 ⟨s, hs, hzu ▸ hconn⟩
    · exact w.2 ⟨s, hs, hzw ▸ hconn⟩

theorem actualMultiClusterComplementGraph_le :
    (G.induce (actualMultiClusterComplementSet S A)).map
      (actualMultiClusterComplementEmbedding S A) ≤ G := by
  rw [← edgeRestriction_actualMultiClusterReveal_eq_induced_complement]
  solve_by_elim [edgeRestriction_le]

theorem actualMultiClusterReveal_eq_subgraphRemovedEdges :
    actualMultiClusterReveal G S A =
      subgraphRemovedEdges
        ((G.induce (actualMultiClusterComplementSet S A)).map
          (actualMultiClusterComplementEmbedding S A)) G := by
  apply Finset.ext
  intro e
  rw [mem_subgraphRemovedEdges]
  have hgraph := congrArg SimpleGraph.edgeSet
    (edgeRestriction_actualMultiClusterReveal_eq_induced_complement (G := G) S A)
  grind [edgeRestriction_edgeSet, Set.mem_sdiff, e.property, coe_mem_openEdges_iff]

/-- Conditioning on the union of actual clusters rooted at a finite seed set
leaves the exact FK law on the induced complement graph. -/
theorem law_filter_actualMultiClusterRecord_map_complement
    (A₀ : Configuration G) :
    ((law G q ξ).filter
      (revealRecordEvent G (actualMultiClusterReveal G S) A₀)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent G
          (actualMultiClusterReveal_consistent S) A₀]
        solve_by_elim [frozenStateEvent_support])).map
        (embeddedConfigurationRestriction
          (G.induce (actualMultiClusterComplementSet S A₀)) G
          (actualMultiClusterComplementEmbedding S A₀)
          (actualMultiClusterComplementGraph_le (G := G) S A₀)) =
      law (G.induce (actualMultiClusterComplementSet S A₀)) q
        (isolatedExtensionPullbackBoundary (actualMultiClusterComplementEmbedding S A₀)
          (frozenBoundary ξ
            (revealRecordConfiguration G (actualMultiClusterReveal G S) A₀).val)) := by
  let C := actualMultiClusterComplementSet S A₀
  let f := actualMultiClusterComplementEmbedding S A₀
  let H := (G.induce C).map f
  let R := actualMultiClusterReveal G S A₀
  let K := revealRecordConfiguration G (actualMultiClusterReveal G S) A₀
  have hR : R = subgraphRemovedEdges H G := id (actualMultiClusterReveal_eq_subgraphRemovedEdges S A₀)
  let K' : RemovedConfiguration G (subgraphRemovedEdges H G) := by
    refine ⟨K.val, ?_⟩
    grind
  have hHG := actualMultiClusterComplementGraph_le S A₀
  have hevent : revealRecordEvent G (actualMultiClusterReveal G S) A₀ =
      frozenStateEvent K' := by
    rw [revealRecordEvent_eq_frozenStateEvent G
      (actualMultiClusterReveal_consistent S) A₀]
    simp [frozenStateEvent, K', K, R, hR]
  have hfiltered :
      (law G q ξ).filter (revealRecordEvent G (actualMultiClusterReveal G S) A₀)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent G
            (actualMultiClusterReveal_consistent S) A₀]
          solve_by_elim [frozenStateEvent_support]) =
      (law G q ξ).filter (frozenStateEvent K')
        (frozenStateEvent_support q ξ (subgraphRemovedEdges H G) K') := by
    simp_all
  simpa [H, f, K, R, C, K', isolatedExtensionPullbackBoundary, hR] using
    (congrArg (fun P : PMF (Configuration G) => PMF.map (embeddedConfigurationRestriction _ G f hHG) P) hfiltered).trans (law_filter_frozen_map_embeddedRestriction (G.induce C) G f hHG q ξ K')

end
end PottsDiscontinuity.FK
