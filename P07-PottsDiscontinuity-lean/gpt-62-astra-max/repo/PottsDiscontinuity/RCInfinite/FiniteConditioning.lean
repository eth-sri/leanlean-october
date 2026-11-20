module

public import PottsDiscontinuity.FK.ConditionalEmbeddedLaw
public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.FK.FiberExpectation

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace PottsDiscontinuity.RCInfinite
open FK FK.FiniteProbability
open scoped Classical
noncomputable section

section Embedded
variable {V W : Type*} [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H)

attribute [local instance] configurationMeasurableSpace
local instance outerEdgeFintype : Fintype H.edgeSet := Fintype.ofFinite _
local instance innerEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _
local instance outerEdgeDecidableEq : DecidableEq H.edgeSet := Classical.decEq _
local instance removedFintype (R : Configuration H) : Fintype (RemovedConfiguration H R) :=
  Fintype.ofFinite _

theorem embedded_filter_probability (θ : Parameters) (ξ : BoundaryCondition W)
    (K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))
    (S : Set (Configuration G)) :
    (((law H θ ξ).filter
      (frozenStateEvent K)
      (frozenStateEvent_support θ ξ (subgraphRemovedEdges (G.map f) H) K)).toMeasure
        ((embeddedConfigurationRestriction G H f hGH) ⁻¹' S)) =
      measure G θ (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) S := by
  have h := congrArg (fun p : PMF (Configuration G) => p.toMeasure S)
    (law_filter_frozen_map_embeddedRestriction G H f hGH θ ξ K)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at h
  exact h

omit [Finite W] in
theorem split_second_fiber (R : Configuration H) (K : RemovedConfiguration H R) :
    {C | (configurationSplitEquiv H R C).2 = K} = frozenStateEvent K := by
  ext C
  exact Subtype.ext_iff

variable (θ : Parameters) (ξ : BoundaryCondition W) (η : BoundaryCondition V)
    (S : Set (Configuration G)) (hS : IsUpperSet S)
include hS

/-- The conditional upper comparison remains valid after intersecting with an
arbitrary event of the exterior edge state. -/
theorem embedded_joint_le
    (hpart : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition ≤ η.partition)
    (T : Set (RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))) :
    (measure H θ ξ
      (((embeddedConfigurationRestriction G H f hGH) ⁻¹' S) ∩
        (fun C => (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).2) ⁻¹' T)).toReal ≤
      (measure G θ η S).toReal *
        (measure H θ ξ
          ((fun C => (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).2) ⁻¹' T)).toReal := by
  let R := subgraphRemovedEdges (G.map f) H
  let out :=
    fun C => (configurationSplitEquiv H R C).2
  have hf : ∀ K, ∃ C ∈ {C | out C = K}, C ∈ (law H θ ξ).support := by
    intro K
    simpa only [out, split_second_fiber] using frozenStateEvent_support θ ξ R K
  apply pmf_joint_le_of_fiber_le_on_T out hf
    ((embeddedConfigurationRestriction G H f hGH) ⁻¹' S) T (measure G θ η S).toReal
  intro K _
  have heq : {C | out C = K} = frozenStateEvent K := split_second_fiber H R K
  have hprob := embedded_filter_probability G H f hGH θ ξ K S
  simp only [heq]
  rw [hprob]
  exact measure_boundary_comparison θ _ η (hpart K) S hS

/-- The conditional lower comparison with the free law also remains valid
after intersecting with an arbitrary exterior-state event. -/
theorem embedded_joint_ge
    (hpart : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      η.partition ≤ (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition)
    (T : Set (RemovedConfiguration H (subgraphRemovedEdges (G.map f) H))) :
    (measure G θ η S).toReal *
        (measure H θ ξ
          ((fun C => (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).2) ⁻¹' T)).toReal ≤
      (measure H θ ξ
        (((embeddedConfigurationRestriction G H f hGH) ⁻¹' S) ∩
          (fun C => (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).2) ⁻¹' T)).toReal := by
  let R := subgraphRemovedEdges (G.map f) H
  let out :=
    fun C => (configurationSplitEquiv H R C).2
  have hf : ∀ K, ∃ C ∈ {C | out C = K}, C ∈ (law H θ ξ).support := by
    intro K
    simpa only [out, split_second_fiber] using frozenStateEvent_support θ ξ R K
  apply pmf_joint_ge_of_fiber_ge out hf
    ((embeddedConfigurationRestriction G H f hGH) ⁻¹' S) T (measure G θ η S).toReal
  intro K
  have heq : {C | out C = K} = frozenStateEvent K := split_second_fiber H R K
  have hprob := embedded_filter_probability G H f hGH θ ξ K S
  simp only [heq]
  rw [hprob]
  exact measure_boundary_comparison θ η _ (hpart K) S hS

end Embedded
end
end PottsDiscontinuity.RCInfinite
