/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: import/namespace relocation; existing FK.Parameters replaces ClusterWeight, permitting all q >= 1 and 0 < p < 1. -/
module

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

section
variable (v : V) (A : Configuration G)
include v A

/-- All actual graph edges incident to the open cluster of `v`, including
closed edges on its boundary. -/
def actualClusterReveal : Configuration G := by
  classical
  exact Finset.univ.filter fun e : G.edgeSet =>
    ∃ u : V, u ∈ e.1 ∧ ActualConnected A v u

theorem actualClusterReveal_mem_iff
    (e : G.edgeSet) :
    e ∈ actualClusterReveal G v A ↔
      ∃ u : V, u ∈ e.1 ∧ ActualConnected A v u := by
  simp [actualClusterReveal]

end

omit [Finite V] in
private theorem openGraph_adj_to_config_mem (A : Configuration G) {u w : V}
    (h : (openGraph A).Adj u w) :
    (⟨s(u,w), G.mem_edgeSet.mpr ((openGraph_le A) h)⟩ : G.edgeSet) ∈ A := by
  have hmem := (openGraph_adj A u w).mp h
  rcases hmem with ⟨e, heA, heq⟩
  grind

omit [Finite V] in
private theorem config_mem_to_openGraph_adj (A : Configuration G) {u w : V}
    (huw : G.Adj u w)
    (he : (⟨s(u,w), G.mem_edgeSet.mpr huw⟩ : G.edgeSet) ∈ A) :
    (openGraph A).Adj u w := by
  rw [openGraph_adj]
  exact ⟨⟨s(u,w), G.mem_edgeSet.mpr huw⟩, he, rfl⟩

section
variable (v : V) (A B : Configuration G)
    (hagree : B ∩ actualClusterReveal G v A = A ∩ actualClusterReveal G v A)
include hagree

private theorem revealed_edge_state_iff
    {e : G.edgeSet} (he : e ∈ actualClusterReveal G v A) :
    e ∈ B ↔ e ∈ A := by
  have h := Finset.ext_iff.mp hagree e
  grind

private theorem actualConnected_mono_reveal :
    ∀ {u : V}, ActualConnected A v u → ActualConnected B v u := by
  intro u hu
  change (openGraph A).Reachable v u at hu
  change (openGraph B).Reachable v u
  rw [SimpleGraph.reachable_iff_reflTransGen] at hu ⊢
  induction hu with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z hprefix hedge ih =>
      have hyA : ActualConnected A v y := by
        change (openGraph A).Reachable v y
        grind [SimpleGraph.reachable_iff_reflTransGen]
      have hG := (openGraph_le A) hedge
      let e : G.edgeSet := ⟨s(y,z), G.mem_edgeSet.mpr hG⟩
      have heA := openGraph_adj_to_config_mem G A hedge
      have heR : e ∈ actualClusterReveal G v A := by
        grind [actualClusterReveal_mem_iff]
      have heB := (revealed_edge_state_iff G v A B hagree heR).mpr heA
      have hedgeB : (openGraph B).Adj y z := by
        exact config_mem_to_openGraph_adj G B hG (by assumption)
      grind

private theorem actualConnected_antitone_reveal :
    ∀ {u : V}, ActualConnected B v u → ActualConnected A v u := by
  intro u hu
  change (openGraph B).Reachable v u at hu
  change (openGraph A).Reachable v u
  rw [SimpleGraph.reachable_iff_reflTransGen] at hu ⊢
  induction hu with
  | refl => exact Relation.ReflTransGen.refl
  | @tail y z hprefix hedge ih =>
      have hyA : ActualConnected A v y := by
        change (openGraph A).Reachable v y
        grind [SimpleGraph.reachable_iff_reflTransGen]
      have hG := (openGraph_le B) hedge
      let e : G.edgeSet := ⟨s(y,z), G.mem_edgeSet.mpr hG⟩
      have heR : e ∈ actualClusterReveal G v A := by
        grind [actualClusterReveal_mem_iff]
      have heB := openGraph_adj_to_config_mem G B hedge
      have heA := (revealed_edge_state_iff G v A B hagree heR).mp heB
      have hedgeA : (openGraph A).Adj y z := by
        exact config_mem_to_openGraph_adj G A hG (by assumption)
      grind

end

/-- Agreement on every edge incident to the seed's actual open cluster makes the
actual open cluster itself identical. -/
theorem actualConnected_iff_of_reveal_agreement
    {v : V} {A B : Configuration G}
    (hagree : B ∩ actualClusterReveal G v A = A ∩ actualClusterReveal G v A)
    (u : V) :
    ActualConnected B v u ↔ ActualConnected A v u := by
  constructor
  · exact actualConnected_antitone_reveal G v A B hagree
  · exact actualConnected_mono_reveal G v A B hagree

end

end PottsDiscontinuity.FK
