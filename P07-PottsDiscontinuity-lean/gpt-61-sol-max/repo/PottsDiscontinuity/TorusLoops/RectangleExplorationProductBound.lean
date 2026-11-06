module
public import Mathlib

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

section

variable (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
include hN hM roots

/-- Adding a new root to the distinct-crossing event implies the old event and
that the new root lies outside every old root cluster. -/
theorem rectangleDistinctRootCrossingEvent_append_projection
    
    (u : FaceVertex N M true) (A : Configuration (rectangleBaseGraph hN hM))
    (hA : A ∈ rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])) :
    A ∈ rectangleDistinctRootCrossingEvent hN hM roots ∧
      u ∉ rectangleRootClusterUnion hN hM roots A := by
  rcases hA with ⟨hcross, hnodup, hdistinct⟩
  have happend : ∀ x ∈ roots, x ∈ roots ++ [u] := by
    grind
  
  
  have hu_not_roots : u ∉ roots := by
    grind
  
  refine ⟨ by
             refine ⟨?_,  (List.nodup_append'.mp hnodup).1 , ?_⟩
             all_goals grind , ?_⟩
  intro huU
  rcases huU with ⟨x, hx, hxu⟩
  
  exact hdistinct x (happend x hx) u
    (List.mem_append.mpr (Or.inr (List.mem_singleton_self u))) (by
                                                                  intro h
                                                                  subst x
                                                                  exact hu_not_roots hx) hxu

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
  
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨root, hroot, hpair⟩
    
    exact hpair ▸  hK.1 root (by simpa using hroot) 
  · intro hp
    have hpB : pair ∈ rectangleLabeledRootClusterObservation hN hM roots B := by
      simp_all
    rcases Finset.mem_image.mp hpB with ⟨root, hroot, hpair⟩
    have hrecord  :=
      hK.1 root (by simpa using hroot)
    have hrecordB :
        (root, rectangleRootClusterFinset hN hM K.val root) ∈
          rectangleLabeledRootClusterObservation hN hM roots B := by
      simp_all
    rcases Finset.mem_image.mp hrecordB with ⟨root', hroot', hrecordEq⟩
    have hrootEq : root' = root := congrArg Prod.fst hrecordEq
    subst root'
    
    apply Finset.mem_image.mpr
    exact ⟨root, by simpa using hroot,  hrecordEq.symm.trans hpair ⟩

/-- Configurations whose exact removed state is consistent with an occurring
observation belong to that observation's full configuration fiber. -/
theorem rectangleObservationRemovedState_preimage_subset_fiber
    
    (b : rectangleRootObservationIndex hN hM roots) :
    {A | rectangleComplementRemovedState hN hM
      (rectangleLabeledObservationVertexSet b.val) A ∈
        rectangleObservationRemovedStateEvent hN hM roots b.val} ⊆
      {A | rectangleRootObservationIndexOf hN hM roots A = b} := by
  obtain ⟨B, hB⟩ := b.property
  
  intro A hA
  let K := rectangleComplementRemovedState hN hM
    (rectangleLabeledObservationVertexSet b.val) A
  
  have hclosed  := hA.2
  have hcluster : ∀ root, root ∈ roots →
      rectangleRootClusterFinset hN hM K.val root =
        rectangleRootClusterFinset hN hM A root := by
    intro root hroot
    
    exact rectangleRemovedState_clusterFinset_eq_of_open_edges_inside
      hN hM (rectangleLabeledObservationVertexSet b.val) A root (by
                                                                   rw [((congrArg rectangleLabeledObservationVertexSet hB).symm.trans
                                                                                                                   (rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots B))]
                                                                   exact ⟨root, hroot, SimpleGraph.Reachable.rfl⟩) hclosed
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
  exact hobsA.trans (rectangleObservationRemovedStateEvent_observation_eq
                       hN hM roots b K hA)

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

end

/-- Old observations on which the new root is still unexplored. -/
def rectangleEligibleRootObservation (hN : Even N) (hM : Even M)
    (roots : List (FaceVertex N M true)) (u : FaceVertex N M true)  :=
  {b | b ∈ rectangleGoodRootObservation hN hM roots ∧
    u ∉ rectangleLabeledObservationVertexSet b.val}

section

variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ)) (roots : List (FaceVertex N M true)) (u : FaceVertex N M true) (hu : u.val.1.val = 0)
include hu

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
  
  have hweighted := rectangleWeightedExplorationRootCrossing_le
    hN hM q U u hu huU T  fun K => And.right 
  
  have hprob (E : Set (Configuration G)) :
      rectangleBaseEventProbability hN hM q E = (p.toMeasure E).toReal := by
    simp [rectangleBaseEventProbability, PottsDiscontinuity.FK.measure,
      p, θ, G]
  
  
  
  
  
  change (p.toMeasure (H ∩ F)).toReal ≤
    rectangleFreeOneArmProbability q (N / 2 - 1) * (p.toMeasure F).toReal
  calc
    (p.toMeasure (H ∩ F)).toReal ≤ (p.toMeasure J).toReal :=  ENNReal.toReal_mono (measure_ne_top p.toMeasure J) (measure_mono  fun ⦃A⦄ hA =>
                                                                                                                                                           And.casesOn hA fun hH hF =>
                                                                                                                                                             And.casesOn hH fun hcross right =>
                                                                                                                                                               And.casesOn right fun hnodup hdistinct =>
                                                                                                                                                                 have hobs := congrArg Subtype.val hF;
                                                                                                                                                                 ⟨rectangleRootCrossing_complement_of_clusterUnion_eq hN hM roots A u U
                                                                                                                                                                     (Eq.trans (Eq.symm (congrArg rectangleLabeledObservationVertexSet hobs))
                                                                                                                                                                       (rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots A))
                                                                                                                                                                     huU
                                                                                                                                                                     (fun x hx hxu =>
                                                                                                                                                                       (rectangleDistinctRootCrossingEvent_append_projection hN hM roots u A hH).right
                                                                                                                                                                         (Exists.intro x ⟨hx, hxu⟩))
                                                                                                                                                                     (hcross u (List.mem_append.mpr (Or.inr (List.mem_singleton_self u)))),
                                                                                                                                                                   Eq.mp
                                                                                                                                                                     (congrArg
                                                                                                                                                                       (fun X =>
                                                                                                                                                                         rectangleComplementRemovedState hN hM (rectangleLabeledObservationVertexSet X) A ∈
                                                                                                                                                                           rectangleObservationRemovedStateEvent hN hM roots X)
                                                                                                                                                                       hobs)
                                                                                                                                                                     (rectangleRemovedState_mem_observationRemovedStateEvent hN hM roots A)⟩ ) 
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (rectangleComplementRemovedState hN hM U ⁻¹' T)).toReal :=  by
                                                                                   grind [rectangleWeightedExplorationConclusion] 
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) * (p.toMeasure F).toReal :=
      mul_le_mul_of_nonneg_left (ENNReal.toReal_mono (measure_ne_top p.toMeasure F) (measure_mono (rectangleObservationRemovedState_preimage_subset_fiber hN hM roots b))) (by
                                              simp [rectangleFreeOneArmProbability])

/-- Summing the eligible observation fibers gives the one-step product bound
for distinct rooted crossings. -/
theorem rectangleDistinctRootCrossingEvent_probability_step
     :
    rectangleBaseEventProbability hN hM q
        (rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])) ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) *
        rectangleBaseEventProbability hN hM q
          (rectangleDistinctRootCrossingEvent hN hM roots) := by
  
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
  let S := rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])
  let T := rectangleEligibleRootObservation hN hM roots u
  let H₀ := rectangleDistinctRootCrossingEvent hN hM roots
  let Hgood := rectangleGoodRootObservation hN hM roots
  
  
  
  
  
  have hH0eq : H₀ = f ⁻¹' Hgood := Set.ext (rectangleDistinctRootCrossingEvent_iff_good_observation hN hM roots)
  have hprob (E : Set (Configuration G)) :
      rectangleBaseEventProbability hN hM q E = (p.toMeasure E).toReal := by
    simp [rectangleBaseEventProbability, PottsDiscontinuity.FK.measure,
      p, θ, G]
  
  calc
    rectangleBaseEventProbability hN hM q S = (p.toMeasure S).toReal := hprob S
    _ ≤ (p.toMeasure (S ∩ f ⁻¹' T)).toReal := ENNReal.toReal_mono (measure_ne_top _ _)
                                          (MeasureTheory.measure_mono (fun ⦃A⦄ hA =>
                                                                         ⟨hA,
                                                                           have hprojection := rectangleDistinctRootCrossingEvent_append_projection hN hM roots u A hA;
                                                                           ⟨(rectangleDistinctRootCrossingEvent_iff_good_observation hN hM roots A).mp hprojection.left, fun huA =>
                                                                             hprojection.right
                                                                               (Eq.mp (congrArg (fun V => u ∈ V) (rectangleLabeledObservationVertexSet_eq_rootClusterUnion hN hM roots A))
                                                                                 huA)⟩⟩))
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (f ⁻¹' T)).toReal := (pmf_joint_le_of_joint_fiber_le_on_T p f (by
                                                                                                   intro b
                                                                                                   simpa [f, p, θ, G] using
                                                                                                     rectangleRootObservationIndex_fiber_has_law_support hN hM q roots b) S T
                                             (rectangleFreeOneArmProbability q (N / 2 - 1)) (by
                                                                                               intro b hb
                                                                                               
                                                                                               rcases (hb) with ⟨_, huU⟩
                                                                                               simpa [f, S] using
                                                                                                 rectangleDistinctRootCrossingEvent_fiber_probability_le
                                                                                                   hN hM q roots u hu b huU))
    _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure (f ⁻¹' Hgood)).toReal := by
      apply mul_le_mul_of_nonneg_left _ (by
                                           simp [rectangleFreeOneArmProbability])
      exact ENNReal.toReal_mono (measure_ne_top _ _)
        (MeasureTheory.measure_mono (Set.preimage_mono  fun b hb => hb.1 ))
    _ = rectangleFreeOneArmProbability q (N / 2 - 1) *
        (p.toMeasure H₀).toReal := by rw [← hH0eq]
    _ = rectangleFreeOneArmProbability q (N / 2 - 1) *
        rectangleBaseEventProbability hN hM q H₀ := by rw [hprob]

end



/-- The distinct-crossing event is unchanged by moving the first root to the
last position in the root list. -/
theorem rectangleDistinctRootCrossingEvent_cons_eq_append
    (hN : Even N) (hM : Even M) (roots : List (FaceVertex N M true))
    (u : FaceVertex N M true) :
    rectangleDistinctRootCrossingEvent hN hM (u :: roots) =
      rectangleDistinctRootCrossingEvent hN hM (roots ++ [u]) := by
  ext A
  constructor
  · rintro ⟨hcross, hnodup, hdistinct⟩
    
    
    refine ⟨?_, ?_, ?_⟩
    · grind
    · grind
    · grind
  · rintro ⟨hcross, hnodup, hdistinct⟩
    have hparts := List.nodup_append'.mp hnodup
    
    
    
    refine ⟨?_, ?_, ?_⟩
    · simp_all
    · simp_all
    · grind

/-- The probability of distinct left-to-right crossings from any finite list
of left-boundary roots is at most the one-arm probability to the list length. -/
theorem rectangleDistinctRootCrossingEvent_probability_le_pow
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (roots : List (FaceVertex N M true))
    (hleft : ∀ u ∈ roots, u.val.1.val = 0) :
    rectangleBaseEventProbability hN hM q
        (rectangleDistinctRootCrossingEvent hN hM roots) ≤
      rectangleFreeOneArmProbability q (N / 2 - 1) ^ roots.length := by
  
  
  induction roots with
  | nil =>
      simp [rectangleDistinctRootCrossingEvent, rectangleBaseEventProbability]
  | cons u roots ih =>
      
      
      
      
      
      rw [ congrArg (rectangleBaseEventProbability hN hM q) (rectangleDistinctRootCrossingEvent_cons_eq_append
                                                                 hN hM roots u) ]
      calc
        rectangleBaseEventProbability hN hM q
            (rectangleDistinctRootCrossingEvent hN hM (roots ++ [u])) ≤
            rectangleFreeOneArmProbability q (N / 2 - 1) *
              rectangleBaseEventProbability hN hM q
                (rectangleDistinctRootCrossingEvent hN hM roots) :=  rectangleDistinctRootCrossingEvent_probability_step
                                                                       hN hM q roots u (hleft u (by simp)) 
        _ ≤ rectangleFreeOneArmProbability q (N / 2 - 1) *
              rectangleFreeOneArmProbability q (N / 2 - 1) ^ roots.length :=
          mul_le_mul_of_nonneg_left (ih (by
                                           aesop)) (by
                                                  simp [rectangleFreeOneArmProbability])
        _ = rectangleFreeOneArmProbability q (N / 2 - 1) ^ (roots.length + 1) := by
          
          ring

end PottsDiscontinuity.TorusLoops
