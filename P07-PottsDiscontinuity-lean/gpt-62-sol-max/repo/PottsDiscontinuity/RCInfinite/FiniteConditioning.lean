module

public import PottsDiscontinuity.FK.ConditionalEmbeddedLaw
public import PottsDiscontinuity.FK.IncreasingEvents
public import PottsDiscontinuity.FK.FiberMeasure

@[expose] public section

open MeasureTheory Set
open scoped BigOperators

namespace PottsDiscontinuity.RCInfinite
open FK FK.FiniteProbability
open scoped Classical
noncomputable section

/-- The free comparison is a lower bound; the wired comparison is an upper bound. -/
def comparisonSign (i : Fin 2) : ℝ := if i = 0 then -1 else 1

@[simp] theorem comparisonSign_zero : comparisonSign 0 = -1 := rfl
@[simp] theorem comparisonSign_one : comparisonSign 1 = 1 := rfl

@[simp] theorem abs_comparisonSign (i : Fin 2) : |comparisonSign i| = 1 := by
  fin_cases i <;> simp

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
      (frozenStateEvent (subgraphRemovedEdges (G.map f) H) K)
      (frozenStateEvent_support θ ξ (subgraphRemovedEdges (G.map f) H) K)).toMeasure
        ((embeddedConfigurationRestriction G H f hGH) ⁻¹' S)) =
      measure G θ (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)) S := by
  have h := congrArg (fun p : PMF (Configuration G) => p.toMeasure S)
    (law_filter_frozen_map_embeddedRestriction G H f hGH θ ξ K)
  rw [PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top] at h
  exact h

omit [Finite W] in
theorem split_second_fiber (R : Configuration H) (K : RemovedConfiguration H R) :
    {C | (configurationSplitEquiv H R C).2 = K} = frozenStateEvent R K := by
  ext C
  exact Subtype.ext_iff

abbrev exteriorState (C : Configuration H) :=
  (configurationSplitEquiv H (subgraphRemovedEdges (G.map f) H) C).2

/-- Domain Markov and partition comparison, integrated over any exterior event. -/
theorem embedded_joint_compare (i : Fin 2) (θ : Parameters) (ξ : BoundaryCondition W)
    (η : BoundaryCondition V) (S : Set (Configuration G)) (hS : IsUpperSet S)
    (T : Set (RemovedConfiguration H (subgraphRemovedEdges (G.map f) H)))
    (hpart : ∀ K : RemovedConfiguration H (subgraphRemovedEdges (G.map f) H),
      let π := (isolatedExtensionPullbackBoundary f (frozenBoundary ξ K.val)).partition
      if i = 0 then η.partition ≤ π else π ≤ η.partition) :
    comparisonSign i * (measure H θ ξ
      (((embeddedConfigurationRestriction G H f hGH) ⁻¹' S) ∩
        exteriorState G H f ⁻¹' T)).toReal ≤
      comparisonSign i * (measure G θ η S).toReal * (measure H θ ξ
        (exteriorState G H f ⁻¹' T)).toReal := by
  have hf K : ∃ C ∈ {C | exteriorState G H f C = K}, C ∈ (law H θ ξ).support := by
    simpa only [exteriorState, split_second_fiber] using
      frozenStateEvent_support θ ξ (subgraphRemovedEdges (G.map f) H) K
  apply pmf_joint_signed_le (law H θ ξ) (exteriorState G H f) hf
    ((embeddedConfigurationRestriction G H f hGH) ⁻¹' S) T (comparisonSign i) (measure G θ η S).toReal
  intro K _
  simp only [Measure.real, exteriorState, split_second_fiber]
  rw [embedded_filter_probability]
  by_cases hi : i = 0
  · simpa [hi] using measure_boundary_comparison θ η _ (by simpa [hi] using hpart K) S hS
  · simpa [comparisonSign, hi] using measure_boundary_comparison θ _ η (by simpa [hi] using hpart K) S hS

end Embedded
end
end PottsDiscontinuity.RCInfinite
