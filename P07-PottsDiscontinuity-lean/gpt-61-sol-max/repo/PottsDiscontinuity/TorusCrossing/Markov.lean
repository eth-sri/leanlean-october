module
public import Mathlib

public import PottsDiscontinuity.FK.ConditionalEmbeddedLaw
public import PottsDiscontinuity.FK.Events

/-!
# Domain Markov property and boundary comparison for an embedded subgraph

A conditioning of the FK measure of a graph `H` on the exact state of all edges outside an
embedded subgraph `G` gives, on `G`, the FK law with the pulled-back induced boundary condition.
We express this as an identity of probabilities of events, and combine it with boundary
comparison.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusCrossing




theorem pmf_filter_toMeasure {X : Type*} [Fintype X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (p : PMF X) (F : Set X) (h : ∃ a ∈ F, a ∈ p.support)
    (T : Set X) :
    (p.filter F h).toMeasure T = p.toMeasure (T ∩ F) / p.toMeasure F := by
  
  
  
  
  rw [ PMF.toMeasure_apply_fintype _ _ ,  PMF.toMeasure_apply_fintype _ _ ,  PMF.toMeasure_apply_fintype _ _ , ENNReal.div_eq_inv_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hxT : x ∈ T
  · rw [Set.indicator_of_mem hxT, PMF.filter_apply,  tsum_fintype _ ]
    by_cases hxF : x ∈ F
    · simp_all <;> grind
    · simp_all
  · simp_all

attribute [local instance] FK.configurationMeasurableSpace

/-- **Domain Markov for an embedded subgraph**, as an identity of probabilities. -/
theorem embedded_frozen_measure_eq {V W : Type*} [Finite V] [Finite W] (G : SimpleGraph V)
    (H : SimpleGraph W) (f : V ↪ W) (hGH : G.map f ≤ H) (q : FK.Parameters)
    (ξ : FK.BoundaryCondition W)
    (K : FK.RemovedConfiguration H (FK.subgraphRemovedEdges (G.map f) H))
    (S : Set (FK.Configuration G)) :
    FK.measure H q ξ ({C | FK.embeddedConfigurationRestriction G H f hGH C ∈ S} ∩
        FK.frozenStateEvent (FK.subgraphRemovedEdges (G.map f) H) K) =
      FK.measure G q (FK.isolatedExtensionPullbackBoundary f (FK.frozenBoundary ξ K.val)) S *
        FK.measure H q ξ (FK.frozenStateEvent (FK.subgraphRemovedEdges (G.map f) H) K) := by
  let : Fintype H.edgeSet := Fintype.ofFinite _
  
  
  have hF := FK.frozenStateEvent_support q ξ (FK.subgraphRemovedEdges (G.map f) H) K
  have h1 : (FK.law G q (FK.isolatedExtensionPullbackBoundary f
      (FK.frozenBoundary ξ K.val))).toMeasure S =
      ((FK.law H q ξ).filter (FK.frozenStateEvent (FK.subgraphRemovedEdges (G.map f) H) K)
        hF).toMeasure
        ( FK.embeddedConfigurationRestriction G H f hGH  ⁻¹' S) := by
    rw [←  FK.law_filter_frozen_map_embeddedRestriction G H f hGH q ξ K , PMF.toMeasure_map_apply _ _ _ measurable_from_top MeasurableSpace.measurableSet_top]
  rw [pmf_filter_toMeasure] at h1
  have hpos : 0 < FK.measure H q ξ
      (FK.frozenStateEvent (FK.subgraphRemovedEdges (G.map f) H) K) := by
    rw [FK.measure_pos_iff]
    obtain ⟨C, hC, _⟩ := hF
    exact ⟨C, hC⟩
  
  change FK.measure H q ξ _ = (FK.law G q _).toMeasure S * FK.measure H q ξ _
  rw [h1]
  change _ = _ / FK.measure H q ξ _ * FK.measure H q ξ _
  rw [ENNReal.div_mul_cancel hpos.ne' (MeasureTheory.measure_ne_top _ _)]
  rfl

end PottsDiscontinuity.TorusCrossing
