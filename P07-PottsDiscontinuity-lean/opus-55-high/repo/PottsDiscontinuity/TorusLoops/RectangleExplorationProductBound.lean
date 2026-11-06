module

public import PottsDiscontinuity.TorusLoops.RectangleExplorationProduct

/-!
# Probability bounds for sequential rectangle exploration

This module turns the weighted one-step estimate into a bound on distinct
rooted crossings, one exact old-cluster observation at a time.
-/

public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.Torus
open PottsDiscontinuity.FK

open scoped Classical

variable {N M : ℕ}

section
variable (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
/-- Adding a new root to the distinct-crossing event implies the old event and
that the new root lies outside every old root cluster. -/
theorem rectangleDistinctRootCrossingEvent_append_projection
    (u : FaceVertex N M true) (A : Configuration (rectangleBaseGraph hN hM))
    (hA : A ∈ rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])) :
    A ∈ rectangleDistinctRootCrossingEvent hN hM roots ∧
      u ∉ rectangleRootClusterUnion hN hM roots A := by
  rcases hA with ⟨hcross, hnodup, hdistinct⟩
  have hroot_event : A ∈ rectangleDistinctRootCrossingEvent hN hM roots := by
    refine ⟨?_, (by grind), ?_⟩ <;> grind
  refine ⟨hroot_event, ?_⟩
  intro huU
  rcases huU with ⟨x, hx, hxu⟩
  grind

/-- A removed state consistent with an occurring labeled observation has that
same complete observation. -/
theorem rectangleObservationRemovedStateEvent_observation_eq
    (b : rectangleRootObservationIndex hN hM roots)
    (K : RemovedConfiguration (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedEdges hN hM
        (rectangleLabeledObservationVertexSet b.val)))
    (hK : K ∈ rectangleObservationRemovedStateEvent hN hM roots b.val) :
    rectangleLabeledRootClusterObservation hN hM roots K.val = b.val := by
  obtain ⟨B, hB⟩ := b.property
  apply Finset.ext
  intro pair
  change pair ∈ roots.toFinset.image
      (fun root => (root, rectangleRootClusterFinset hN hM K.val root)) ↔
    pair ∈ b.val
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨root, hroot, hpair⟩
    have hrecord :=
      hK.1 root (by simpa using hroot)
    grind
  · intro hp
    have hpB : pair ∈ rectangleLabeledRootClusterObservation hN hM roots B := by
      simp_all
    rcases Finset.mem_image.mp hpB with ⟨root, hroot, hpair⟩
    have hrecord :=
      hK.1 root (by simp_all)
    have hrecordB :
        (root, rectangleRootClusterFinset hN hM K.val root) ∈
          rectangleLabeledRootClusterObservation hN hM roots B := by
      simp_all
    rcases Finset.mem_image.mp hrecordB with ⟨root', hroot', hrecordEq⟩
    grind

/-- Configurations whose exact removed state is consistent with an occurring
observation belong to that observation's full configuration fiber. -/
theorem rectangleObservationRemovedState_preimage_subset_fiber
    (b : rectangleRootObservationIndex hN hM roots) :
    {A | rectangleComplementRemovedState hN hM
      (rectangleLabeledObservationVertexSet b.val) A ∈
        rectangleObservationRemovedStateEvent hN hM roots b.val} ⊆
      {A | rectangleRootObservationIndexOf hN hM roots A = b} := by
  obtain ⟨B, hB⟩ := b.property
  have hU :=
    (congrArg rectangleLabeledObservationVertexSet hB).symm.trans
      (rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots B)
  intro A hA
  let K := rectangleComplementRemovedState hN hM
    (rectangleLabeledObservationVertexSet b.val) A
  have hobsK := rectangleObservationRemovedStateEvent_observation_eq
    hN hM roots b K hA
  have hcluster : ∀ root, root ∈ roots →
      rectangleRootClusterFinset hN hM K.val root =
        rectangleRootClusterFinset hN hM A root := by
    intro root hroot
    have hrootU : root ∈ rectangleLabeledObservationVertexSet b.val := by
      rw [hU]
      exact ⟨root, hroot, SimpleGraph.Reachable.rfl⟩
    exact rectangleRemovedState_clusterFinset_eq_of_open_edges_inside
      hN hM (rectangleLabeledObservationVertexSet b.val) A root hrootU hA.2
  have hobsA : rectangleLabeledRootClusterObservation hN hM roots A =
      rectangleLabeledRootClusterObservation hN hM roots K.val := by
    apply Finset.ext
    intro pair
    constructor
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨root, hroot, hpair⟩
      apply Finset.mem_image.mpr
      refine ⟨root, hroot, ?_⟩
      exact (congrArg (fun C => (root, C)) (hcluster root (by simpa using hroot))).trans hpair
    · intro hp
      rcases Finset.mem_image.mp hp with ⟨root, hroot, hpair⟩
      apply Finset.mem_image.mpr
      refine ⟨root, hroot, ?_⟩
      exact (congrArg (fun C => (root, C)) (hcluster root (by simpa using hroot))).symm.trans hpair
  apply Subtype.ext
  exact hobsA.trans hobsK

/-- The new-root transfer is stable under replacing its cluster union by any
extensionally equal explored vertex set. -/
theorem rectangleRootCrossing_complement_of_clusterUnion_eq
    (A : Configuration (rectangleBaseGraph hN hM)) (u : FaceVertex N M true)
    (U : Set (FaceVertex N M true))
    (hU : U = rectangleRootClusterUnion hN hM roots A)
    (huU : u ∉ U)
    (hseparate : ∀ x ∈ roots,
      ¬ ActualConnected (rectangleBaseGraph hN hM) A x u)
    (hcross : A ∈ rectangleRootCrossingEvent hN hM u) :
    rectangleComplementRootCrossingEvent hN hM U u huU
      (embeddedConfigurationRestriction (rectangleComplementGraph hN hM U)
        (rectangleBaseGraph hN hM) (rectangleComplementEmbedding U)
        (rectangleComplementGraph_map_le hN hM U) A) := by
  subst U
  exact rectangleRootCrossing_complement_of_distinct_roots
    hN hM roots A u hseparate hcross

/-- Old observations on which the new root is still unexplored. -/
def rectangleEligibleRootObservation (u : FaceVertex N M true) :
    Set (rectangleRootObservationIndex hN hM roots) :=
  {b | b ∈ rectangleGoodRootObservation hN hM roots ∧
    u ∉ rectangleLabeledObservationVertexSet b.val}
end

section
variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (roots : List (FaceVertex N M true)) (u : FaceVertex N M true) (hu : u.val.1.val = 0)
include q hu
/-- On each old-cluster observation fiber where the new root is outside the
explored union, the event of one more distinct crossing is bounded by the
free one-arm probability times the mass of that fiber. -/
theorem rectangleDistinctRootCrossingEvent_fiber_probability_le
    (b : rectangleRootObservationIndex hN hM roots)
    (huU : u ∉ rectangleLabeledObservationVertexSet b.val) :
    let p := law (rectangleBaseGraph hN hM) (rectangleFKParameters q)
      (BoundaryCondition.free ∅)
    (p.toMeasure
      (rectangleDistinctRootCrossingEvent hN hM (roots ++ [u]) ∩
        {A | rectangleRootObservationIndexOf hN hM roots A = b})).toReal ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure
          {A | rectangleRootObservationIndexOf hN hM roots A = b}).toReal := by
  let G := rectangleBaseGraph hN hM
  let θ := rectangleFKParameters q
  let p := law G θ (BoundaryCondition.free ∅)
  let O := b.val
  let U := rectangleLabeledObservationVertexSet O
  let T := rectangleObservationRemovedStateEvent hN hM roots O
  let H := rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])
  let F := {A | rectangleRootObservationIndexOf hN hM roots A = b}
  let J := rectangleComplementJointEvent hN hM U
    (rectangleComplementRootCrossingEvent hN hM U u huU) T
  have hT : ∀ K ∈ T, ∀ ⦃x y : FaceVertex N M true⦄,
      (openGraph G K.val).Adj x y → x ∈ U ∧ y ∈ U := by
    intro K hK x y hxy
    exact hK.2 hxy
  have hweighted := rectangleWeightedExplorationRootCrossing_le
    hN hM q U u hu huU T hT
  have hsub : H ∩ F ⊆ J := by
    intro A hA
    rcases hA with ⟨hH, hF⟩
    have hprojection := rectangleDistinctRootCrossingEvent_append_projection
      hN hM roots u A hH
    rcases hH with ⟨hcross, hnodup, hdistinct⟩
    have hseparate : ∀ x ∈ roots,
        ¬ ActualConnected G A x u := by
      intro x hx hxu
      exact hprojection.2 ⟨x, hx, hxu⟩
    have hobs :=
      congrArg Subtype.val hF
    have hUconfig :=
      (congrArg rectangleLabeledObservationVertexSet hobs).symm.trans
        (rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots A)
    have hcomp := rectangleRootCrossing_complement_of_clusterUnion_eq
      hN hM roots A u U hUconfig huU hseparate (hcross u (List.mem_append.mpr (Or.inr (List.mem_singleton_self u))))
    have hstate : rectangleComplementRemovedState hN hM U A ∈ T := by
      have heq := congrArg (fun X =>
        rectangleComplementRemovedState hN hM
            (rectangleLabeledObservationVertexSet X) A ∈
          rectangleObservationRemovedStateEvent hN hM roots X) hobs
      exact heq.mp (rectangleRemovedState_mem_observationRemovedStateEvent
        hN hM roots A)
    tauto
  have hprob (E : Set (Configuration G)) :
      rectangleBaseEventProbability hN hM q E = (p.toMeasure E).toReal := by
    simp [rectangleBaseEventProbability, PottsDiscontinuity.FK.measure,
      p, θ, G]
  have hstateSub :
      (rectangleComplementRemovedState hN hM U ⁻¹' T) ⊆ F :=
    rectangleObservationRemovedState_preimage_subset_fiber hN hM roots b
  have hmono : (p.toMeasure (H ∩ F)).toReal ≤ (p.toMeasure J).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (MeasureTheory.measure_mono hsub)
  have hweightedReal : (p.toMeasure J).toReal ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (rectangleComplementRemovedState hN hM U ⁻¹' T)).toReal := by
    grind [rectangleWeightedExplorationConclusion, rectangleBaseEventProbability, rectangleFreeOneArmProbability, rectangleComplementRemovedState]
  have hstateMono :
      (p.toMeasure (rectangleComplementRemovedState hN hM U ⁻¹' T)).toReal ≤
        (p.toMeasure F).toReal :=
    ENNReal.toReal_mono (measure_ne_top _ _)
      (MeasureTheory.measure_mono hstateSub)
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
    simp [rectangleFreeOneArmProbability]
  calc
    (p.toMeasure (H ∩ F)).toReal ≤ (p.toMeasure J).toReal := hmono
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (rectangleComplementRemovedState hN hM U ⁻¹' T)).toReal := hweightedReal
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) * (p.toMeasure F).toReal :=
      mul_le_mul_of_nonneg_left hstateMono hρ

/-- Summing the eligible observation fibers gives the one-step product bound
for distinct rooted crossings. -/
theorem rectangleDistinctRootCrossingEvent_probability_step
     :
    rectangleBaseEventProbability hN hM q
        (rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])) ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        rectangleBaseEventProbability hN hM q
          (rectangleDistinctRootCrossingEvent hN hM roots) := by
  let : Finite (rectangleRootObservationIndex hN hM roots) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  let : Fintype (rectangleRootObservationIndex hN hM roots) := Fintype.ofFinite _
  let G := rectangleBaseGraph hN hM
  let θ := rectangleFKParameters q
  let p := law G θ (BoundaryCondition.free ∅)
  let f := rectangleRootObservationIndexOf hN hM roots
  let S := rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])
  let T := rectangleEligibleRootObservation hN hM roots u
  let H₀ := rectangleDistinctRootCrossingEvent hN hM roots
  let Hgood := rectangleGoodRootObservation hN hM roots
  have hf : ∀ b, ∃ A ∈ {A | f A = b}, A ∈ p.support := by
    intro b
    simpa [f, p, θ, G] using
      rectangleRootObservationIndex_fiber_has_law_support hN hM q roots b
  have hFiber : ∀ b ∈ T,
      (p.toMeasure (S ∩ {A | f A = b})).toReal ≤
        rectangleFreeOneArmProbability q (N / 2 - 1) *
          (p.toMeasure {A | f A = b}).toReal := by
    intro b hb
    have hEligible : b ∈ rectangleEligibleRootObservation hN hM roots u := by
      omega
    rcases hEligible with ⟨_, huU⟩
    simpa [f, S] using
      rectangleDistinctRootCrossingEvent_fiber_probability_le
        hN hM q roots u hu b huU
  have hsum := RCInfinite.pmf_joint_le_of_joint_fiber_le p f hf S T
    (rectangleFreeOneArmProbability q (N / 2 - 1)) hFiber
  have hnewSubset : S ⊆ S ∩ f ⁻¹' T := by
    intro A hA
    have hprojection := rectangleDistinctRootCrossingEvent_append_projection
      hN hM roots u A hA
    have hgood : f A ∈ Hgood := by
      tauto
    have houtside : u ∉ rectangleLabeledObservationVertexSet (f A).val := by
      intro huA
      have hUeq := rectangleLabeledObservationVertexSet_eq_rootClusterUnion
        hN hM roots A
      have huUnion :=
        (congrArg (fun V => u ∈ V) hUeq).mp huA
      grind
    tauto
  have hTsub : T ⊆ Hgood := by
    intro b hb
    exact hb.1
  have hH0eq : H₀ = f ⁻¹' Hgood := by
    ext A
    exact rectangleDistinctRootCrossingEvent_iff_good_observation
      hN hM roots A
  have hprob (E : Set (Configuration G)) :
      rectangleBaseEventProbability hN hM q E = (p.toMeasure E).toReal := by
    simp [rectangleBaseEventProbability, PottsDiscontinuity.FK.measure,
      p, θ, G]
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
    simp [rectangleFreeOneArmProbability]
  calc
    rectangleBaseEventProbability hN hM q S = (p.toMeasure S).toReal := hprob S
    _ ≤ (p.toMeasure (S ∩ f ⁻¹' T)).toReal :=
      ENNReal.toReal_mono (measure_ne_top _ _)
        (MeasureTheory.measure_mono hnewSubset)
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (f ⁻¹' T)).toReal := hsum
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (f ⁻¹' Hgood)).toReal := by
      apply mul_le_mul_of_nonneg_left _ hρ
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (MeasureTheory.measure_mono (Set.preimage_mono hTsub))
    _ = rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure H₀).toReal := by grind
    _ = rectangleFreeOneArmProbability q (N / 2 - 1) *
        rectangleBaseEventProbability hN hM q H₀ := by grind
end

section
variable {α : Type*} (u x : α) (roots : List α)

end

section
variable (hN : Even N) (hM : Even M)
/-- The distinct-crossing event is unchanged by moving the first root to the
last position in the root list. -/
theorem rectangleDistinctRootCrossingEvent_cons_eq_append
    (roots : List (FaceVertex N M true))
    (u : FaceVertex N M true) :
    rectangleDistinctRootCrossingEvent hN hM (u :: roots) =
      rectangleDistinctRootCrossingEvent hN hM (roots ++ [u]) := by
  ext A
  constructor
  · rintro ⟨hcross, hnodup, hdistinct⟩
    refine ⟨?_, ?_, ?_⟩ <;> grind
  · rintro ⟨hcross, hnodup, hdistinct⟩
    refine ⟨?_, ?_, ?_⟩ <;> grind

/-- The probability of distinct left-to-right crossings from any finite list
of left-boundary roots is at most the one-arm probability to the list length. -/
theorem rectangleDistinctRootCrossingEvent_probability_le_pow
    (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true))
    (hleft : ∀ u ∈ roots, u.val.1.val = 0) :
    rectangleBaseEventProbability hN hM q
        (rectangleDistinctRootCrossingEvent hN hM roots) ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) ^ roots.length := by
  have hρ : 0 ≤ rectangleFreeOneArmProbability q (N / 2 - 1) := by
    simp [rectangleFreeOneArmProbability]
  induction roots with
  | nil =>
      simp [rectangleDistinctRootCrossingEvent, rectangleBaseEventProbability,
        PottsDiscontinuity.FK.measure]
  | cons u roots ih =>
      have htail : ∀ x ∈ roots, x.val.1.val = 0 := by
        grind
      have hstep := rectangleDistinctRootCrossingEvent_probability_step
        hN hM q roots u (by grind)
      have hperm := rectangleDistinctRootCrossingEvent_cons_eq_append
        hN hM roots u
      have hprobEq :
          rectangleBaseEventProbability hN hM q
              (rectangleDistinctRootCrossingEvent hN hM (u :: roots)) =
            rectangleBaseEventProbability hN hM q
              (rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])) :=
        by grind
      rw [hprobEq]
      calc
        rectangleBaseEventProbability hN hM q
            (rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])) ≤
            rectangleFreeOneArmProbability q (N / 2 - 1) *
              rectangleBaseEventProbability hN hM q
                (rectangleDistinctRootCrossingEvent hN hM roots) := hstep
        _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
              rectangleFreeOneArmProbability q (N / 2 - 1) ^ roots.length :=
          mul_le_mul_of_nonneg_left (ih htail) hρ
        _ = rectangleFreeOneArmProbability q (N / 2 - 1) ^ (roots.length + 1) := by
          ring
end

end PottsDiscontinuity.TorusLoops
