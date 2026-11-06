/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: import/namespace relocation; existing FK.Parameters replaces ClusterWeight, permitting all q >= 1 and 0 < p < 1. -/
module
public import Mathlib

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
    (A : Configuration G) (u : V)  :=
  ∃ s, s ∈ S ∧ ActualConnected G A s u

/-- All edges incident to any actual open cluster rooted at a seed in `S`. -/
def actualMultiClusterReveal (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G) : Configuration G := by
  classical
  exact Finset.univ.filter fun e : G.edgeSet =>
    ∃ u : V, u ∈ e.1 ∧ actualMultiClusterConnected G S A u

section

variable (S : Finset V)
include S

theorem actualMultiClusterReveal_mem_iff  (A : Configuration G)
    (e : G.edgeSet) :
    e ∈ actualMultiClusterReveal G S A ↔
      ∃ u : V, u ∈ e.1 ∧ ∃ s, s ∈ S ∧ ActualConnected G A s u := by
  grind +locals

theorem actualClusterReveal_subset_multi  (A : Configuration G)
    {s : V} (hs : s ∈ S) :
    actualClusterReveal G s A ⊆ actualMultiClusterReveal G S A := by
  intro e he
  rw [actualMultiClusterReveal_mem_iff]
  rcases (actualClusterReveal_mem_iff G s A e).mp he with ⟨u, hu, hconn⟩
  aesop

section

variable (A B : Configuration G) (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A)
include hagree

private theorem single_reveal_agreement_of_multi
     
    {s : V} (hs : s ∈ S) :
    B ∩ actualClusterReveal G s A = A ∩ actualClusterReveal G s A := by
  
  apply Finset.ext
  intro e
  simp only [Finset.mem_inter]
  have heq := Finset.ext_iff.mp hagree e
  simp only [Finset.mem_inter] at heq
  constructor
  · rintro ⟨heB, heSingle⟩
    have heMulti := actualClusterReveal_subset_multi S A hs heSingle
    simp_all
  · rintro ⟨heA, heSingle⟩
    have heMulti := actualClusterReveal_subset_multi S A hs heSingle
    simp_all

theorem actualMultiClusterConnected_iff_of_reveal_agreement
     
    (u : V) :
    actualMultiClusterConnected G S B u ↔ actualMultiClusterConnected G S A u := by
  constructor
  · rintro ⟨s, hs, hconn⟩
    exact ⟨s, hs, (actualConnected_iff_of_reveal_agreement G s A B
      (single_reveal_agreement_of_multi S A B hagree hs) u).mp hconn⟩
  · rintro ⟨s, hs, hconn⟩
    exact ⟨s, hs, (actualConnected_iff_of_reveal_agreement G s A B
      (single_reveal_agreement_of_multi S A B hagree hs) u).mpr hconn⟩

theorem actualMultiClusterReveal_consistent
      :
    actualMultiClusterReveal G S B = actualMultiClusterReveal G S A := by
  ext e
  rw [actualMultiClusterReveal_mem_iff, actualMultiClusterReveal_mem_iff]
  constructor
  · rintro ⟨u, hu, s, hs, hconn⟩
    exact ⟨u, hu, s, hs, (actualConnected_iff_of_reveal_agreement G s A B
      (single_reveal_agreement_of_multi S A B hagree hs) u).mp hconn⟩
  · rintro ⟨u, hu, s, hs, hconn⟩
    exact ⟨u, hu, s, hs, (actualConnected_iff_of_reveal_agreement G s A B
      (single_reveal_agreement_of_multi S A B hagree hs) u).mpr hconn⟩

end

end

def actualMultiClusterComplementSet (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G)  :=
  {u | ¬ actualMultiClusterConnected G S A u}

def actualMultiClusterComplementEmbedding (G : SimpleGraph V) (S : Finset V)
    (A : Configuration G) : actualMultiClusterComplementSet G S A ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

section

variable (S : Finset V) (A : Configuration G)


theorem edgeRestriction_actualMultiClusterReveal_eq_induced_complement
     :
    edgeRestriction G (actualMultiClusterReveal G S A) =
      (G.induce (actualMultiClusterComplementSet G S A)).map
        (actualMultiClusterComplementEmbedding G S A) := by
  ext x y
  constructor
  · intro hxy
    
    rcases  by
              simpa [edgeRestriction] using hxy  with ⟨hAdj, hNot⟩
    have hnotConn :
        ¬ actualMultiClusterConnected G S A x ∧
        ¬ actualMultiClusterConnected G S A y := by
      constructor
      · intro hx
        apply hNot
        rcases hx with ⟨s, hs, hconn⟩
        
        
        simpa using  (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A)
                       ⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩).mpr (by
                                                                grind [actualMultiClusterReveal_mem_iff]) 
      · intro hy
        apply hNot
        rcases hy with ⟨s, hs, hconn⟩
        
        
        simpa using  (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A)
                       ⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩).mpr (by
                                                                grind [actualMultiClusterReveal_mem_iff]) 
    apply (SimpleGraph.map_adj (actualMultiClusterComplementEmbedding G S A)
      (G.induce (actualMultiClusterComplementSet G S A)) x y).2
    refine ⟨⟨x, hnotConn.1⟩, ⟨y, hnotConn.2⟩, ?_, rfl, rfl⟩
    exact SimpleGraph.induce_adj.mpr hAdj
  · intro hxy
    rcases (SimpleGraph.map_adj (actualMultiClusterComplementEmbedding G S A)
      (G.induce (actualMultiClusterComplementSet G S A)) x y).1 hxy with
      ⟨u, w, hAdjInduced, hux, hwy⟩
    have hAdj  := SimpleGraph.induce_adj.mp hAdjInduced
    
    
    subst x
    subst y
    rw [edgeRestriction, SimpleGraph.deleteEdges_adj]
    refine ⟨hAdj, ?_⟩
    intro hmem
    
    rcases (actualMultiClusterReveal_mem_iff S A _).mp ((coe_mem_openEdges_iff G (actualMultiClusterReveal G S A) ⟨s(↑u, ↑w), (SimpleGraph.mem_edgeSet G).mpr hAdj⟩).mp hmem) with
      ⟨z, hz, s, hs, hconn⟩
    rcases (Sym2.mem_iff').mp hz with hzu | hzw
    · exact u.2 ⟨s, hs, hzu ▸ hconn⟩
    · exact w.2 ⟨s, hs, hzw ▸ hconn⟩

theorem actualMultiClusterComplementGraph_le
     :
    (G.induce (actualMultiClusterComplementSet G S A)).map
      (actualMultiClusterComplementEmbedding G S A) ≤ G := by
                                                             solve_by_elim [_root_.SimpleGraph.map_comap_le]

theorem actualMultiClusterReveal_eq_subgraphRemovedEdges
     :
    actualMultiClusterReveal G S A =
      subgraphRemovedEdges
        ((G.induce (actualMultiClusterComplementSet G S A)).map
          (actualMultiClusterComplementEmbedding G S A)) G := by
  apply Finset.ext
  intro e
  rw [mem_subgraphRemovedEdges]
  have hgraph := congrArg SimpleGraph.edgeSet
    (edgeRestriction_actualMultiClusterReveal_eq_induced_complement (G := G) S A)
  rw [edgeRestriction_edgeSet] at hgraph
  rw [← hgraph]
  
  simp [coe_mem_openEdges_iff]

end

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
  have hR : R = subgraphRemovedEdges H G := actualMultiClusterReveal_eq_subgraphRemovedEdges S A₀
  let K' : RemovedConfiguration G (subgraphRemovedEdges H G) := by
    refine ⟨K.val, ?_⟩
    rw [← hR]
    exact K.property
  have hHG : H ≤ G := actualMultiClusterComplementGraph_le S A₀
  
  have hevent : revealRecordEvent G (actualMultiClusterReveal G S) A₀ =
      frozenStateEvent (subgraphRemovedEdges H G) K' := by
    rw [revealRecordEvent_eq_frozenStateEvent G (actualMultiClusterReveal G S)
      (actualMultiClusterReveal_consistent S) A₀]
    
    simp [frozenStateEvent, K', K, R, hR]
  have hfiltered :
      (law G q ξ).filter (revealRecordEvent G (actualMultiClusterReveal G S) A₀)
        (by
          rw [revealRecordEvent_eq_frozenStateEvent G (actualMultiClusterReveal G S)
            (actualMultiClusterReveal_consistent S) A₀]
          exact frozenStateEvent_support q ξ (actualMultiClusterReveal G S A₀)
            (revealRecordConfiguration G (actualMultiClusterReveal G S) A₀)) =
      (law G q ξ).filter (frozenStateEvent (subgraphRemovedEdges H G) K')
        (frozenStateEvent_support q ξ (subgraphRemovedEdges H G) K') := by
    simp_all
  have hfilter := congrArg
     (PMF.map (embeddedConfigurationRestriction (G.induce C) G f hHG))  hfiltered
  simpa  using
    hfilter.trans (law_filter_frozen_map_embeddedRestriction
                     (G.induce C) G f hHG q ξ K')

end
end PottsDiscontinuity.FK
