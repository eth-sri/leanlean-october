module

public import PottsDiscontinuity.TorusLoops.RectangleExplorationProduct

/-!
# Probability bounds for sequential rectangle exploration

This module turns the weighted one-step estimate into a bound on distinct
rooted crossings, one exact old-cluster observation at a time.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK

open scoped Classical

variable {N M : ℕ}

theorem rectangleDistinctRootCrossingEvent_cons_projection
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (u : FaceVertex N M true) (A : Configuration (rectangleBaseGraph hN hM))
    (hA : A ∈ rectangleDistinctRootCrossingEvent hN hM (u :: roots)) :
    A ∈ rectangleDistinctRootCrossingEvent hN hM roots ∧
      u ∉ rectangleRootClusterUnion hN hM roots A := by
  rcases hA with ⟨hcross, hnodup, hdistinct⟩
  obtain ⟨hu_not_roots, hrootNodup⟩ := List.nodup_cons.mp hnodup
  refine ⟨⟨fun x hx => hcross x (List.mem_cons_of_mem u hx), hrootNodup,
    fun x hx y hy => hdistinct x (List.mem_cons_of_mem u hx) y (List.mem_cons_of_mem u hy)⟩, ?_⟩
  rintro ⟨x, hx, hxu⟩
  exact hdistinct x (List.mem_cons_of_mem u hx) u List.mem_cons_self
    (fun h => hu_not_roots (h ▸ hx)) hxu

theorem rectangleObservationRemovedStateEvent_observation_eq
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (b : rectangleRootObservationIndex hN hM roots)
    (K : RemovedConfiguration (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedEdges hN hM
        (rectangleLabeledObservationVertexSet b.val)))
    (hK : K ∈ rectangleObservationRemovedStateEvent hN hM roots b.val) :
    rectangleLabeledRootClusterObservation hN hM roots K.val = b.val := by
  obtain ⟨B, hB⟩ := b.property
  ext pair
  change pair ∈ roots.toFinset.image
      (fun root => (root, rectangleRootClusterFinset hN hM K.val root)) ↔
    pair ∈ b.val
  refine ⟨?_, ?_⟩
  · rintro hp
    rcases Finset.mem_image.mp hp with ⟨root, hroot, rfl⟩
    exact hK.1 root (by simpa using hroot)
  · intro hp
    have hpB : pair ∈ rectangleLabeledRootClusterObservation hN hM roots B := by
      rwa [hB]
    rcases Finset.mem_image.mp hpB with ⟨root, hroot, hpair⟩
    have hrecordB : (root, rectangleRootClusterFinset hN hM K.val root) ∈
        rectangleLabeledRootClusterObservation hN hM roots B := by
      rw [hB]; exact hK.1 root (by simpa using hroot)
    rcases Finset.mem_image.mp hrecordB with ⟨root', _, hrecordEq⟩
    cases congrArg Prod.fst hrecordEq
    exact Finset.mem_image.mpr ⟨root, hroot, hrecordEq.symm.trans hpair⟩

theorem rectangleObservationRemovedState_preimage_subset_fiber
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (b : rectangleRootObservationIndex hN hM roots) :
    {A | rectangleComplementRemovedState hN hM
      (rectangleLabeledObservationVertexSet b.val) A ∈
        rectangleObservationRemovedStateEvent hN hM roots b.val} ⊆
      {A | rectangleRootObservationIndexOf hN hM roots A = b} := by
  obtain ⟨B, hB⟩ := b.property
  have hU : rectangleLabeledObservationVertexSet b.val =
      rectangleRootClusterUnion hN hM roots B :=
    (congrArg rectangleLabeledObservationVertexSet hB).symm.trans
      (rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots B)
  intro A hA
  let K := rectangleComplementRemovedState hN hM
    (rectangleLabeledObservationVertexSet b.val) A
  have hcluster (root : FaceVertex N M true) (hroot : root ∈ roots) :
      rectangleRootClusterFinset hN hM K.val root =
        rectangleRootClusterFinset hN hM A root :=
    rectangleRemovedState_clusterFinset_eq_of_open_edges_inside
      hN hM (rectangleLabeledObservationVertexSet b.val) A root
      (hU.symm ▸ ⟨root, hroot, SimpleGraph.Reachable.rfl⟩) hA.2
  have hobsA : rectangleLabeledRootClusterObservation hN hM roots A =
      rectangleLabeledRootClusterObservation hN hM roots K.val := by
    refine Finset.image_congr fun root hroot => ?_
    rw [hcluster root (by simpa using hroot)]
  exact Subtype.ext (hobsA.trans (rectangleObservationRemovedStateEvent_observation_eq hN hM roots b K hA))

theorem rectangleRootCrossing_complement_of_clusterUnion_eq
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (A : Configuration (rectangleBaseGraph hN hM)) (u : FaceVertex N M true)
    (U : Set (FaceVertex N M true))
    (hU : U = rectangleRootClusterUnion hN hM roots A) (huU : u ∉ U)
    (hseparate : ∀ x ∈ roots, ¬ ActualConnected (rectangleBaseGraph hN hM) A x u)
    (hcross : A ∈ rectangleRootCrossingEvent hN hM u) :
    rectangleComplementRootCrossingEvent hN hM U u huU
      (embeddedConfigurationRestriction (rectangleComplementGraph hN hM U)
        (rectangleBaseGraph hN hM) (rectangleComplementEmbedding U)
        (rectangleComplementGraph_map_le hN hM U) A) := by
  subst U
  exact rectangleRootCrossing_complement_of_distinct_roots hN hM roots A u hseparate hcross

def rectangleEligibleRootObservation (hN : Even N) (hM : Even M)
    (roots : List (FaceVertex N M true)) (u : FaceVertex N M true) :
    Set (rectangleRootObservationIndex hN hM roots) :=
  {b | b ∈ rectangleGoodRootObservation hN hM roots ∧
    u ∉ rectangleLabeledObservationVertexSet b.val}

theorem rectangleDistinctRootCrossingEvent_fiber_probability_le
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true)) (u : FaceVertex N M true)
    (hu : u.val.1.val = 0)
    (b : rectangleRootObservationIndex hN hM roots)
    (huU : u ∉ rectangleLabeledObservationVertexSet b.val) :
    let p := law (rectangleBaseGraph hN hM) (rectangleFKParameters q)
      (BoundaryCondition.free ∅)
    (p.toMeasure
      (rectangleDistinctRootCrossingEvent hN hM (u :: roots) ∩
        {A | rectangleRootObservationIndexOf hN hM roots A = b})).toReal ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure
          {A | rectangleRootObservationIndexOf hN hM roots A = b}).toReal := by
  classical
  let G := rectangleBaseGraph hN hM
  let θ := rectangleFKParameters q
  let p := law G θ (BoundaryCondition.free ∅)
  let O := b.val
  let U := rectangleLabeledObservationVertexSet O
  let T := rectangleObservationRemovedStateEvent hN hM roots O
  let H := rectangleDistinctRootCrossingEvent hN hM (u :: roots)
  let F := {A | rectangleRootObservationIndexOf hN hM roots A = b}
  let J := rectangleComplementJointEvent hN hM U
    (rectangleComplementRootCrossingEvent hN hM U u huU) T
  have hweighted := rectangleWeightedExplorationRootCrossing_le
    hN hM q U u hu huU T fun _ hK _ _ hxy => hK.2 hxy
  have hsub : H ∩ F ⊆ J := by
    rintro A ⟨hH, hF⟩
    have hprojection := rectangleDistinctRootCrossingEvent_cons_projection hN hM roots u A hH
    rcases hH with ⟨hcross, _, _⟩
    have huCross : A ∈ rectangleRootCrossingEvent hN hM u := hcross u List.mem_cons_self
    have hseparate : ∀ x ∈ roots, ¬ ActualConnected G A x u :=
      fun x hx hxu => hprojection.2 ⟨x, hx, hxu⟩
    have hobs : rectangleLabeledRootClusterObservation hN hM roots A = O :=
      congrArg Subtype.val hF
    have hUconfig : U = rectangleRootClusterUnion hN hM roots A :=
      (congrArg rectangleLabeledObservationVertexSet hobs).symm.trans
        (rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots A)
    have hcomp := rectangleRootCrossing_complement_of_clusterUnion_eq
      hN hM roots A u U hUconfig huU hseparate huCross
    have hstate : rectangleComplementRemovedState hN hM U A ∈ T := by
      dsimp [U, T]
      rw [← hobs]
      exact rectangleRemovedState_mem_observationRemovedStateEvent hN hM roots A
    exact ⟨hcomp, hstate⟩
  have hprob (E : Set (Configuration G)) :
      rectangleBaseEventProbability hN hM q E = (p.toMeasure E).toReal := by
    simp [rectangleBaseEventProbability, PottsDiscontinuity.FK.measure, p, θ, G]
  have hweightedReal : (p.toMeasure J).toReal ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (rectangleComplementRemovedState hN hM U ⁻¹' T)).toReal := by
    simpa [rectangleWeightedExplorationConclusion, hprob] using hweighted
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
    simp [rectangleFreeOneArmProbability]
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (MeasureTheory.measure_mono hsub)).trans <|
    hweightedReal.trans <| mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (measure_ne_top _ _) (MeasureTheory.measure_mono
        (rectangleObservationRemovedState_preimage_subset_fiber hN hM roots b))) hρ

theorem rectangleDistinctRootCrossingEvent_probability_step
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true)) (u : FaceVertex N M true)
    (hu : u.val.1.val = 0) :
    rectangleBaseEventProbability hN hM q
        (rectangleDistinctRootCrossingEvent hN hM (u :: roots)) ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        rectangleBaseEventProbability hN hM q
          (rectangleDistinctRootCrossingEvent hN hM roots) := by
  classical
  let : Fintype (FaceVertex N M true) := Fintype.ofFinite _
  let : Fintype (Finset (FaceVertex N M true × Finset (FaceVertex N M true))) := inferInstance
  let : Finite (rectangleRootObservationIndex hN hM roots) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let : Fintype (rectangleRootObservationIndex hN hM roots) := Fintype.ofFinite _
  let : MeasurableSpace (rectangleRootObservationIndex hN hM roots) := ⊤
  let : MeasurableSingletonClass (rectangleRootObservationIndex hN hM roots) := inferInstance
  let G := rectangleBaseGraph hN hM
  let θ := rectangleFKParameters q
  let p := law G θ (BoundaryCondition.free ∅)
  let f := rectangleRootObservationIndexOf hN hM roots
  let S := rectangleDistinctRootCrossingEvent hN hM (u :: roots)
  let T := rectangleEligibleRootObservation hN hM roots u
  let H₀ := rectangleDistinctRootCrossingEvent hN hM roots
  let Hgood := rectangleGoodRootObservation hN hM roots
  have hsum := pmf_joint_le_of_joint_fiber_le_on_T p f
    (fun b => by simpa [f, p, θ, G] using rectangleRootObservationIndex_fiber_has_law_support hN hM q roots b)
    S T (rectangleFreeOneArmProbability q (N / 2 - 1))
    fun b hb => by
      simpa [f, S] using rectangleDistinctRootCrossingEvent_fiber_probability_le hN hM q roots u hu b hb.2
  have hnewSubset : S ⊆ S ∩ f ⁻¹' T := fun A hA => by
    have hprojection := rectangleDistinctRootCrossingEvent_cons_projection hN hM roots u A hA
    refine ⟨hA, (rectangleDistinctRootCrossingEvent_iff_good_observation hN hM roots A).mp hprojection.1,
      fun huA => hprojection.2 ?_⟩
    rwa [← rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots A]
  have hH0eq : H₀ = f ⁻¹' Hgood :=
    Set.ext (rectangleDistinctRootCrossingEvent_iff_good_observation hN hM roots)
  have hprob (E : Set (Configuration G)) :
      rectangleBaseEventProbability hN hM q E = (p.toMeasure E).toReal := by
    simp [rectangleBaseEventProbability, PottsDiscontinuity.FK.measure, p, θ, G]
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
    simp [rectangleFreeOneArmProbability]
  rw [hprob S, hprob H₀, hH0eq]
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (MeasureTheory.measure_mono hnewSubset)).trans <|
    hsum.trans <| mul_le_mul_of_nonneg_left
      (ENNReal.toReal_mono (measure_ne_top _ _) (MeasureTheory.measure_mono (Set.preimage_mono fun _ hb => hb.1)))
      hρ

theorem rectangleDistinctRootCrossingEvent_probability_le_pow
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true))
    (hleft : ∀ u ∈ roots, u.val.1.val = 0) :
    rectangleBaseEventProbability hN hM q
        (rectangleDistinctRootCrossingEvent hN hM roots) ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) ^ roots.length := by
  classical
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
    simp [rectangleFreeOneArmProbability]
  induction roots with
  | nil =>
      simp [rectangleDistinctRootCrossingEvent, rectangleBaseEventProbability,
        PottsDiscontinuity.FK.measure]
  | cons u roots ih =>
      calc rectangleBaseEventProbability hN hM q
            (rectangleDistinctRootCrossingEvent hN hM (u :: roots))
        _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
              rectangleBaseEventProbability hN hM q
                (rectangleDistinctRootCrossingEvent hN hM roots) :=
            rectangleDistinctRootCrossingEvent_probability_step hN hM q roots u
              (hleft u List.mem_cons_self)
        _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
              rectangleFreeOneArmProbability q (N / 2 - 1) ^ roots.length :=
            mul_le_mul_of_nonneg_left (ih fun x hx => hleft x (List.mem_cons_of_mem u hx)) hρ
        _ = rectangleFreeOneArmProbability q (N / 2 - 1) ^ (roots.length + 1) := by
            rw [pow_succ']

end PottsDiscontinuity.TorusLoops
