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

section
variable (G : SimpleGraph V) (S : Finset V) (A : Configuration G)
/-- A vertex belongs to the union of the actual open clusters rooted at `S`. -/
def actualMultiClusterConnected (u : V) : Prop :=
  ∃ s, s ∈ S ∧ ActualConnected G A s u

/-- All edges incident to any actual open cluster rooted at a seed in `S`. -/
def actualMultiClusterReveal  : Configuration G := by
  classical
  exact Finset.univ.filter fun e : G.edgeSet =>
    ∃ u : V, u ∈ e.1 ∧ actualMultiClusterConnected G S A u
end

section
variable (S : Finset V) (A : Configuration G)
theorem actualMultiClusterReveal_mem_iff (e : G.edgeSet) :
    e ∈ actualMultiClusterReveal G S A ↔
      ∃ u : V, u ∈ e.1 ∧ ∃ s, s ∈ S ∧ ActualConnected G A s u := by
  classical
  change (e ∈ Finset.univ.filter fun e : G.edgeSet =>
    ∃ u : V, u ∈ e.1 ∧ actualMultiClusterConnected G S A u) ↔ _
  simp
  exact Iff.rfl

theorem actualClusterReveal_subset_multi {s : V} (hs : s ∈ S) :
    actualClusterReveal G s A ⊆ actualMultiClusterReveal G S A := by
  intro e he
  rw [actualMultiClusterReveal_mem_iff]
  rcases (actualClusterReveal_mem_iff G s A e).mp he with ⟨u, hu, hconn⟩
  grind
end

section
variable (S : Finset V) (A B : Configuration G) (hagree : B ∩ actualMultiClusterReveal G S A = A ∩ actualMultiClusterReveal G S A)
include hagree
theorem single_reveal_agreement_of_multi
    {s : V} (hs : s ∈ S) :
    B ∩ actualClusterReveal G s A = A ∩ actualClusterReveal G s A := by
  apply Finset.ext
  intro e
  simp only [Finset.mem_inter]
  have heq := Finset.ext_iff.mp hagree e
  simp at heq
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

section
variable (G : SimpleGraph V) (S : Finset V) (A : Configuration G)
def actualMultiClusterComplementSet  : Set V :=
  {u | ¬ actualMultiClusterConnected G S A u}

def actualMultiClusterComplementEmbedding  : actualMultiClusterComplementSet G S A ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩
end

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
    have hxy' : G.Adj x y ∧ s(x,y) ∉ openEdges G (actualMultiClusterReveal G S A) := by
      simp_all [edgeRestriction]
    rcases hxy' with ⟨hAdj, hNot⟩
    have hnotConn :
        ¬ actualMultiClusterConnected G S A x ∧
        ¬ actualMultiClusterConnected G S A y := by
      constructor
      · intro hx
        apply hNot
        rcases hx with ⟨s, hs, hconn⟩
        have hR : (⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
            actualMultiClusterReveal G S A := by
          rw [actualMultiClusterReveal_mem_iff]
          grind
        have hOpen := (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A)
          ⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩).mpr hR
        omega
      · intro hy
        apply hNot
        rcases hy with ⟨s, hs, hconn⟩
        have hR : (⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
            actualMultiClusterReveal G S A := by
          rw [actualMultiClusterReveal_mem_iff]
          grind
        have hOpen := (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A)
          ⟨s(x,y), G.mem_edgeSet.mpr hAdj⟩).mpr hR
        omega
    apply (SimpleGraph.map_adj (actualMultiClusterComplementEmbedding G S A)
      (G.induce (actualMultiClusterComplementSet G S A)) x y).2
    refine ⟨⟨x, hnotConn.1⟩, ⟨y, hnotConn.2⟩, ?_, rfl, rfl⟩
    simp_all
  · intro hxy
    rcases (SimpleGraph.map_adj (actualMultiClusterComplementEmbedding G S A)
      (G.induce (actualMultiClusterComplementSet G S A)) x y).1 hxy with
      ⟨u, w, hAdjInduced, hux, hwy⟩
    have hAdj := SimpleGraph.induce_adj.mp hAdjInduced
    have hux' : u.val = x := hux
    have hwy' : w.val = y := hwy
    subst x
    subst y
    refine ⟨hAdj, ?_⟩
    intro hmem
    have hR : (⟨s(u,w), G.mem_edgeSet.mpr hAdj⟩ : G.edgeSet) ∈
        actualMultiClusterReveal G S A := by
      apply (coe_mem_openEdges_iff G (actualMultiClusterReveal G S A)
        ⟨s(u,w), G.mem_edgeSet.mpr hAdj⟩).mp
      simp_all
    rcases (actualMultiClusterReveal_mem_iff S A _).mp hR with
      ⟨z, hz, s, hs, hconn⟩
    rcases (Sym2.mem_iff').mp hz with hzu | hzw
    · exact u.2 ⟨s, hs, hzu ▸ hconn⟩
    · exact w.2 ⟨s, hs, hzw ▸ hconn⟩

theorem actualMultiClusterComplementGraph_le
     :
    (G.induce (actualMultiClusterComplementSet G S A)).map
      (actualMultiClusterComplementEmbedding G S A) ≤ G := by
  rw [← edgeRestriction_actualMultiClusterReveal_eq_induced_complement]
  exact edgeRestriction_le G (actualMultiClusterReveal G S A)

theorem actualMultiClusterReveal_eq_subgraphRemovedEdges
     :
    actualMultiClusterReveal G S A =
      subgraphRemovedEdges
        ((G.induce (actualMultiClusterComplementSet G S A)).map
          (actualMultiClusterComplementEmbedding G S A)) G := by
  apply Finset.ext
  intro e
  simp
  have hgraph := congrArg SimpleGraph.edgeSet
    (edgeRestriction_actualMultiClusterReveal_eq_induced_complement S A)
  rw [edgeRestriction_edgeSet] at hgraph
  rw [← hgraph]
  simp [e.property, coe_mem_openEdges_iff]
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
  have hR : R = subgraphRemovedEdges H G := by
    simpa [R, H, C, f] using
      (actualMultiClusterReveal_eq_subgraphRemovedEdges S A₀)
  let K' : RemovedConfiguration G (subgraphRemovedEdges H G) := by
    refine ⟨K.val, ?_⟩
    grind
  have hHG : H ≤ G := by
    change (G.induce (actualMultiClusterComplementSet G S A₀)).map
      (actualMultiClusterComplementEmbedding G S A₀) ≤ G
    simp [actualMultiClusterComplementGraph_le]
  have hconditional := law_filter_frozen_map_embeddedRestriction
    (G.induce C) G f hHG q ξ K'
  have hevent : revealRecordEvent G (actualMultiClusterReveal G S) A₀ =
      frozenStateEvent (subgraphRemovedEdges H G) K' := by
    rw [revealRecordEvent_eq_frozenStateEvent G (actualMultiClusterReveal G S)
      (actualMultiClusterReveal_consistent S) A₀]
    grind [frozenStateEvent]
  aesop

end
end PottsDiscontinuity.FK
