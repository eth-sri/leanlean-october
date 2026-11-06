module
public import Mathlib

public import PottsDiscontinuity.TorusExploration.FilterUpperBound
public import PottsDiscontinuity.FK.ConditionalLaw
public import PottsDiscontinuity.FK.SubgraphComparison
public import PottsDiscontinuity.FK.BoundaryPartitionLaw

/-! Closing all edges outside a subgraph leaves its exact free FK law. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK
variable {V : Type*} [Finite V] {G H : SimpleGraph V}
noncomputable section
open scoped Classical
local instance closedSubgraphSmallEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance closedSubgraphLargeEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance closedSubgraphLargeEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _

/-- The exact state in which every removed original edge is closed. -/
def closedSubgraphRecord (G H : SimpleGraph V) : RemovedConfiguration H (subgraphRemovedEdges G H) :=
  ⟨∅,Finset.empty_subset _⟩

/-- Read the original subgraph configuration from the full remaining coordinates. -/
def subgraphRemainderRead (hGH : G ≤ H) (C : Configuration H)  :=
  (subgraphRemainingConfigurationEquiv hGH).symm
    (configurationSplitEquiv H (subgraphRemovedEdges G H) C).1

section

variable (hGH : G ≤ H)
include hGH

/-- The conditional law is exactly free, since all frozen open-edge sets are empty. -/
theorem filter_closedSubgraph_map  (θ : Parameters) :
    ((law H θ (BoundaryCondition.free ∅)).filter
      (frozenStateEvent (subgraphRemovedEdges G H) (closedSubgraphRecord G H))
      (frozenStateEvent_support θ (BoundaryCondition.free ∅)
        (subgraphRemovedEdges G H) (closedSubgraphRecord G H))).map (subgraphRemainderRead hGH) =
      law G θ (BoundaryCondition.free ∅) := by
  let R := subgraphRemovedEdges G H
  let K := closedSubgraphRecord G H
  let P := (law H θ (BoundaryCondition.free ∅)).filter
    (frozenStateEvent R K) (frozenStateEvent_support θ (BoundaryCondition.free ∅) R K)
  have he : P.map (subgraphRemainderRead hGH) =
      (P.map  fun C => (configurationSplitEquiv H R C).1 ).map
        (subgraphRemainingConfigurationEquiv hGH).symm := by
    rw [PMF.map_comp]
    rfl
  
  rw [he,law_filter_frozen_map_remaining]
  rw [← law_subgraphRemaining_map hGH θ (frozenBoundary (BoundaryCondition.free ∅) K.val),PMF.map_comp]
  have hid : (subgraphRemainingConfigurationEquiv hGH).symm ∘
      subgraphRemainingConfigurationEquiv hGH = id := by  simp
  rw [hid,PMF.map_id]
  apply law_eq_of_boundary_partition_eq
  change componentSetoid H (BoundaryCondition.free ∅) ∅ = _
  rw [componentSetoid_empty]

lemma closedSubgraph_reconstruct  (C : Configuration H)
    (hC : C ∈ frozenStateEvent (subgraphRemovedEdges G H) (closedSubgraphRecord G H)) :
    subgraphConfigurationEmbedding hGH (subgraphRemainderRead hGH C) = C := Eq.mp
                                                                              (congrArg (Eq ((subgraphConfigurationEmbedding hGH) (subgraphRemainderRead hGH C)))
                                                                                (Finset.sdiff_eq_self_of_disjoint (Finset.disjoint_iff_inter_eq_empty.mpr hC)))
                                                                              (congrArg Subtype.val
                                                                                (Equiv.apply_symm_apply (subgraphRemainingConfigurationEquiv hGH)
                                                                                  ((configurationSplitEquiv H (subgraphRemovedEdges G H)) C).1))

/-- The full-law probability of a subgraph event with all other edges closed
is at most its exact free subgraph probability. -/
theorem closedSubgraph_joint_le  (θ : Parameters) (E : Set (Configuration G)) :
    FK.FiniteProbability.expectation (law H θ (BoundaryCondition.free ∅))
      ((frozenStateEvent (subgraphRemovedEdges G H) (closedSubgraphRecord G H) ∩
         subgraphRemainderRead hGH  ⁻¹' E).indicator fun _ => (1 : ℝ)) ≤
      FK.FiniteProbability.expectation (law G θ (BoundaryCondition.free ∅))
        (E.indicator fun _ => (1 : ℝ)) := by
  
  refine (joint_expectation_le_filter (law H θ (BoundaryCondition.free ∅))
            (frozenStateEvent (subgraphRemovedEdges G H) (closedSubgraphRecord G H))
            ( subgraphRemainderRead hGH  ⁻¹' E)
            (frozenStateEvent_support θ (BoundaryCondition.free ∅) _ _)).trans_eq ?_
  change FK.FiniteProbability.expectation
    ((law H θ (BoundaryCondition.free ∅)).filter
      (frozenStateEvent (subgraphRemovedEdges G H) (closedSubgraphRecord G H)) _)
    (fun C => E.indicator (fun _ => 1) (subgraphRemainderRead hGH C)) = _
  rw [← FK.FiniteProbability.expectation_map,filter_closedSubgraph_map]

end

end
end PottsDiscontinuity.TorusExploration
