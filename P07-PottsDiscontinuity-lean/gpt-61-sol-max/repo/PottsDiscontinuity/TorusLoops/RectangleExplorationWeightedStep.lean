module
public import Mathlib

public import PottsDiscontinuity.TorusLoops.RectangleExplorationFibers
public import PottsDiscontinuity.TorusLoops.RectangleExplorationStep

/-!
# Weighted one-step exploration estimate

The fixed-state conditional bound can be averaged over any selected collection
of removed-edge states whose open edges stay in the explored region.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.Torus
open PottsDiscontinuity.CorrLength
open PottsDiscontinuity.Zhang
open PottsDiscontinuity.FK

noncomputable section

variable {N M : ℕ}

/-- The rectangle FK probability of an event, with the large graph and free
boundary condition bundled to keep exploration estimates readable. -/
@[irreducible] noncomputable def rectangleBaseEventProbability (hN : Even N) (hM : Even M)
    (q : Set.Ici (1 : ℝ)) (E : Set (Configuration (rectangleBaseGraph hN hM)))  :=
  (measure (rectangleBaseGraph hN hM) (rectangleFKParameters q)
    (BoundaryCondition.free ∅) E).toReal

local instance explorationWeightedOuterEdgeFintype (hN : Even N) (hM : Even M) :
    Fintype (rectangleBaseGraph hN hM).edgeSet := Fintype.ofFinite _
local instance explorationWeightedOuterEdgeDecidableEq (hN : Even N) (hM : Even M) :
    DecidableEq (rectangleBaseGraph hN hM).edgeSet := Classical.decEq _

private theorem split_second_fiber {V : Type*} (G : SimpleGraph V) [DecidableEq G.edgeSet] (R : Configuration G)
    (K : RemovedConfiguration G R) :
    {C | (configurationSplitEquiv G R C).2 = K} = frozenStateEvent R K := by
  ext C
  have hs : ∀ e ,
      e ∈ (configurationSplitEquiv G R C).2.val ↔ e ∈ C ∧ e ∈ R := by
    
    simp [configurationSplitEquiv]
  constructor
  · intro h
    apply Finset.ext
    aesop
  · intro h
    apply Subtype.ext
    apply Finset.ext
    intro e
    
    exact (hs e).trans (by simpa only [Finset.mem_inter] using  Finset.ext_iff.mp h e )

/-- Edges of the rectangle outside its induced complement graph. -/
noncomputable def rectangleComplementRemovedEdges (hN : Even N) (hM : Even M)
    (U : Set (FaceVertex N M true))  :=
  subgraphRemovedEdges
    ((rectangleComplementGraph hN hM U).map (rectangleComplementEmbedding U))
    (rectangleBaseGraph hN hM)

/-- The exact removed-edge state for a fixed explored vertex set. -/
noncomputable def rectangleComplementRemovedState (hN : Even N) (hM : Even M)
    (U : Set (FaceVertex N M true)) (C : Configuration (rectangleBaseGraph hN hM))  :=
  (configurationSplitEquiv (rectangleBaseGraph hN hM)
    (rectangleComplementRemovedEdges hN hM U) C).2

/-- The joint event of a rooted crossing in the complement and a selected
exact state of its removed edges. -/
noncomputable def rectangleComplementJointEvent
    (hN : Even N) (hM : Even M) (U : Set (FaceVertex N M true))
    (E : Set (Configuration (rectangleComplementGraph hN hM U)))
    (T : Set (RemovedConfiguration (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedEdges hN hM U)))  :=
   embeddedConfigurationRestriction (rectangleComplementGraph hN hM U)
    (rectangleBaseGraph hN hM) (rectangleComplementEmbedding U)
    (rectangleComplementGraph_map_le hN hM U) ⁻¹' E  ∩
       rectangleComplementRemovedState hN hM U ⁻¹' T 

/-- Free infinite-volume one-arm probability at radius `k` in the rotated
lattice. -/
@[irreducible] noncomputable def rectangleFreeOneArmProbability
    (q : Set.Ici (1 : ℝ)) (k : ℕ)  :=
   ((Classical.choose (freeBoxLimit_existsUnique (rectangleFKParameters q))
    (oneArmEvent k) : NNReal) : ℝ) 

/-- The weighted exploration inequality, with its full rectangle event and
probability content exposed by this definition. -/
@[irreducible] noncomputable def rectangleWeightedExplorationConclusion
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (U : Set (FaceVertex N M true)) (u : FaceVertex N M true) (huU : u ∉ U)
    (T : Set (RemovedConfiguration (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedEdges hN hM U)))  :=
  rectangleBaseEventProbability hN hM q
      (rectangleComplementJointEvent hN hM U
        (rectangleComplementRootCrossingEvent hN hM U u huU) T) ≤
    rectangleFreeOneArmProbability q (N / 2 - 1) *
      rectangleBaseEventProbability hN hM q
        (rectangleComplementRemovedState hN hM U ⁻¹' T)

/-- A selected exterior-state event and the next rooted crossing occur with
probability at most the free one-arm probability times the probability of the
selected exterior event. -/
theorem rectangleWeightedExplorationRootCrossing_le
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (U : Set (FaceVertex N M true)) (u : FaceVertex N M true)
    (hu : u.val.1.val = 0) (huU : u ∉ U)
    (T : Set (RemovedConfiguration (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedEdges hN hM U)))
    (hT : ∀ K ∈ T, ∀ ⦃x y : FaceVertex N M true⦄,
      (openGraph (rectangleBaseGraph hN hM) K.val).Adj x y → x ∈ U ∧ y ∈ U) :
    rectangleWeightedExplorationConclusion hN hM q U u huU T := by
  let G := rectangleBaseGraph hN hM
  let I := rectangleComplementGraph hN hM U
  let f := rectangleComplementEmbedding U
  let hIG := rectangleComplementGraph_map_le hN hM U
  let θ := rectangleFKParameters q
  let E := rectangleComplementRootCrossingEvent hN hM U u huU
  let R := subgraphRemovedEdges (I.map f) G
  let out  :=
    fun C => (configurationSplitEquiv G R C).2
  let p := law G θ (BoundaryCondition.free ∅)
  let ρ :=   (Classical.choose (freeBoxLimit_existsUnique θ))
    (oneArmEvent (N / 2 - 1))  
  let S  :=
     embeddedConfigurationRestriction I G f hIG  ⁻¹' E
  
  have hf : ∀ K, ∃ C ∈ {C | out C = K}, C ∈ p.support := by
    intro K
    simpa only [out, split_second_fiber] using
      frozenStateEvent_support θ (BoundaryCondition.free ∅) R K
  have hcond : ∀ K ∈  T ,
      ((p.filter {C | out C = K} (hf K)).toMeasure S).toReal ≤ ρ := by
    intro K hKT
    
    have hconditional := rectangleConditionalRootCrossing_le_freeOneArm
      hN hM q U u hu huU K (hT K hKT)
    have hfiber : {C | out C = K} = frozenStateEvent R K :=
      split_second_fiber G R K
    have hfilter : p.filter {C | out C = K} (hf K) =
        (law G θ (BoundaryCondition.free ∅)).filter
          (frozenStateEvent R K)
          (frozenStateEvent_support θ (BoundaryCondition.free ∅) R K) := by
      simp only [p, hfiber]
    have hmeas : Measurable (embeddedConfigurationRestriction I G f hIG) := by
      fun_prop
    have hmap :
        (((law G θ (BoundaryCondition.free ∅)).filter
          (frozenStateEvent R K)
          (frozenStateEvent_support θ (BoundaryCondition.free ∅) R K)).map
          (embeddedConfigurationRestriction I G f hIG)).toMeasure E =
        ((law G θ (BoundaryCondition.free ∅)).filter
          (frozenStateEvent R K)
          (frozenStateEvent_support θ (BoundaryCondition.free ∅) R K)).toMeasure
          ( embeddedConfigurationRestriction I G f hIG  ⁻¹' E) := by
      exact PMF.toMeasure_map_apply _ _ _ hmeas
        (Set.toFinite E).measurableSet
    calc
      ((p.filter {C | out C = K} (hf K)).toMeasure S).toReal =
          (((law G θ (BoundaryCondition.free ∅)).filter
            (frozenStateEvent R K)
            (frozenStateEvent_support θ (BoundaryCondition.free ∅) R K)).toMeasure
              ( embeddedConfigurationRestriction I G f hIG  ⁻¹' E)).toReal := by
        rw [hfilter]
      _ = ((((law G θ (BoundaryCondition.free ∅)).filter
          (frozenStateEvent R K)
          (frozenStateEvent_support θ (BoundaryCondition.free ∅) R K)).map
          (embeddedConfigurationRestriction I G f hIG)).toMeasure E).toReal := by
        rw [hmap]
      _ ≤ ρ := by omega
  
  
  
  have hjointEvent :
      rectangleComplementJointEvent hN hM U E T = S ∩ out ⁻¹'  T  := by
    rfl
  have hprob (A : Set (Configuration G)) :
      rectangleBaseEventProbability hN hM q A = (p.toMeasure A).toReal := by
    simp [rectangleBaseEventProbability, PottsDiscontinuity.FK.measure,
      p, θ, G]
  have hρ : rectangleFreeOneArmProbability q (N / 2 - 1) = ρ := by
    unfold rectangleFreeOneArmProbability
    dsimp 
  unfold rectangleWeightedExplorationConclusion
  rw [hprob, hjointEvent, hprob, hρ]
  exact  pmf_joint_le_of_fiber_le_on_T p out hf S (T) ρ hcond 

end

end PottsDiscontinuity.TorusLoops
