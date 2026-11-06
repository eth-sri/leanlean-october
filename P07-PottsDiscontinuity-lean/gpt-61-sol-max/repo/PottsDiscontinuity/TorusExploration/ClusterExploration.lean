/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: import/namespace relocation; existing FK.Parameters replaces ClusterWeight, permitting all q >= 1 and 0 < p < 1. -/
module
public import Mathlib

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import PottsDiscontinuity.FK.Graph

@[expose] public section

namespace PottsDiscontinuity.FK


noncomputable section

variable {V : Type*} [Finite V] (G : SimpleGraph V)

local instance clusterExplorationEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance clusterExplorationEdgeDecidableEq : DecidableEq G.edgeSet := Classical.decEq _

/-- All actual graph edges incident to the open cluster of `v`, including
closed edges on its boundary. -/
def actualClusterReveal (v : V) (A : Configuration G) : Configuration G := by
  classical
  exact Finset.univ.filter fun e : G.edgeSet =>
    ∃ u : V, u ∈ e.1 ∧ ActualConnected G A v u

theorem actualClusterReveal_mem_iff (v : V) (A : Configuration G)
    (e : G.edgeSet) :
    e ∈ actualClusterReveal G v A ↔
      ∃ u : V, u ∈ e.1 ∧ ActualConnected G A v u := by
  simp [actualClusterReveal]

omit [Finite V] in
private theorem openGraph_adj_to_config_mem (A : Configuration G) {u w : V}
    (h : (openGraph G A).Adj u w) :
    (⟨s(u,w), G.mem_edgeSet.mpr ((openGraph_le G A) h)⟩ : G.edgeSet) ∈ A := by
  
  rcases  (openGraph_adj G A u w).mp h  with ⟨e, heA, heq⟩
  all_goals aesop

omit [Finite V] in
private theorem config_mem_to_openGraph_adj (A : Configuration G) {u w : V}
    (huw : G.Adj u w)
    (he : (⟨s(u,w), G.mem_edgeSet.mpr huw⟩ : G.edgeSet) ∈ A) :
    (openGraph G A).Adj u w := by
  rw [openGraph_adj]
  exact ⟨⟨s(u,w), G.mem_edgeSet.mpr huw⟩, he, rfl⟩

section

variable (v : V) (A B : Configuration G) (hagree : B ∩ actualClusterReveal G v A = A ∩ actualClusterReveal G v A)
include hagree

private theorem revealed_edge_state_iff
    
    {e : G.edgeSet} (he : e ∈ actualClusterReveal G v A) :
    e ∈ B ↔ e ∈ A := by
  have h := Finset.ext_iff.mp hagree e
  grind

private theorem actualConnected_mono_reveal
     :
    ∀ {u : V}, ActualConnected G A v u → ActualConnected G B v u := by
  intro u hu
  change (openGraph G A).Reachable v u at hu
  change (openGraph G B).Reachable v u
  rw [SimpleGraph.reachable_iff_reflTransGen] at hu ⊢
  induction hu with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z hprefix hedge ih =>
      have hyA : ActualConnected G A v y := by
        change (openGraph G A).Reachable v y
        rw [SimpleGraph.reachable_iff_reflTransGen]
        exact hprefix
      have hG  := (openGraph_le G A) hedge
      
      
      
      
      
      exact Relation.ReflTransGen.tail ih (config_mem_to_openGraph_adj G B hG ((revealed_edge_state_iff G v A B hagree (by
                                                                                                                                       grind +locals)).mpr (openGraph_adj_to_config_mem G A hedge)))

private theorem actualConnected_antitone_reveal
     :
    ∀ {u : V}, ActualConnected G B v u → ActualConnected G A v u := by
  intro u hu
  change (openGraph G B).Reachable v u at hu
  change (openGraph G A).Reachable v u
  rw [SimpleGraph.reachable_iff_reflTransGen] at hu ⊢
  induction hu with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z hprefix hedge ih =>
      have hyA : ActualConnected G A v y := by
        change (openGraph G A).Reachable v y
        rw [SimpleGraph.reachable_iff_reflTransGen]
        exact ih
      have hG  := (openGraph_le G B) hedge
      
      
      
      
      
      exact Relation.ReflTransGen.tail ih (config_mem_to_openGraph_adj G A hG ((revealed_edge_state_iff G v A B hagree (by
                                                                                                                                       grind +locals)).mp (openGraph_adj_to_config_mem G B hedge)))

/-- Agreement on every edge incident to the seed's actual open cluster makes the
actual open cluster itself identical. -/
theorem actualConnected_iff_of_reveal_agreement
    
    (u : V) :
    ActualConnected G B v u ↔ ActualConnected G A v u := by
  grind [actualConnected_antitone_reveal, actualConnected_mono_reveal]

end

end

end PottsDiscontinuity.FK
