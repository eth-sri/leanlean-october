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
  grind [openEdges, openGraph_adj]

omit [Finite V] in
private theorem config_mem_to_openGraph_adj (A : Configuration G) {u w : V}
    (huw : G.Adj u w)
    (he : (⟨s(u,w), G.mem_edgeSet.mpr huw⟩ : G.edgeSet) ∈ A) :
    (openGraph G A).Adj u w := by
  rw [openGraph_adj]
  exact ⟨⟨s(u,w), G.mem_edgeSet.mpr huw⟩, he, rfl⟩

/-- Agreement on every edge incident to the seed's actual open cluster makes the
actual open cluster itself identical. -/
theorem actualConnected_iff_of_reveal_agreement
    (v : V) (A B : Configuration G)
    (hagree : B ∩ actualClusterReveal G v A = A ∩ actualClusterReveal G v A)
    (u : V) :
    ActualConnected G B v u ↔ ActualConnected G A v u := by
  have hstep {y z} (hy : (openGraph G A).Reachable v y) :
      (openGraph G B).Adj y z ↔ (openGraph G A).Adj y z := by
    have he {h : G.Adj y z} :
        (⟨s(y,z), G.mem_edgeSet.mpr h⟩ : G.edgeSet) ∈ B ↔
          (⟨s(y,z), G.mem_edgeSet.mpr h⟩ : G.edgeSet) ∈ A := by
      have hr : (⟨s(y,z), G.mem_edgeSet.mpr h⟩ : G.edgeSet) ∈ actualClusterReveal G v A :=
        (actualClusterReveal_mem_iff ..).2 ⟨y, by simp, hy⟩
      simpa [hr] using Finset.ext_iff.mp hagree ⟨s(y,z), G.mem_edgeSet.mpr h⟩
    exact ⟨fun hb => config_mem_to_openGraph_adj G A (openGraph_le G B hb)
      ((he (h := openGraph_le G B hb)).1 (openGraph_adj_to_config_mem G B hb)),
      fun ha => config_mem_to_openGraph_adj G B (openGraph_le G A ha)
        ((he (h := openGraph_le G A ha)).2 (openGraph_adj_to_config_mem G A ha))⟩
  simp only [ActualConnected, SimpleGraph.reachable_iff_reflTransGen]
  constructor <;> intro h <;> induction h with
  | refl => rfl
  | tail hp he ih =>
    grind [SimpleGraph.reachable_iff_reflTransGen]

end

end PottsDiscontinuity.FK
