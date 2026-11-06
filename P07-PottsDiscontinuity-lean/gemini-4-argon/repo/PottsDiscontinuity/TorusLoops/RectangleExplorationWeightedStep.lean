module

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
    (q : Set.Ici (1 : ℝ)) (E : Set (Configuration (rectangleBaseGraph hN hM))) : ℝ :=
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
  simp [Subtype.ext_iff, Finset.ext_iff, configurationSplitEquiv, frozenStateEvent]

/-- Edges of the rectangle outside its induced complement graph. -/
noncomputable def rectangleComplementRemovedEdges (hN : Even N) (hM : Even M)
    (U : Set (FaceVertex N M true)) : Configuration (rectangleBaseGraph hN hM) :=
  subgraphRemovedEdges
    ((rectangleComplementGraph hN hM U).map (rectangleComplementEmbedding U))
    (rectangleBaseGraph hN hM)

/-- The exact removed-edge state for a fixed explored vertex set. -/
noncomputable def rectangleComplementRemovedState (hN : Even N) (hM : Even M)
    (U : Set (FaceVertex N M true)) (C : Configuration (rectangleBaseGraph hN hM)) :
    RemovedConfiguration (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedEdges hN hM U) :=
  (configurationSplitEquiv (rectangleBaseGraph hN hM)
    (rectangleComplementRemovedEdges hN hM U) C).2

/-- The joint event of a rooted crossing in the complement and a selected
exact state of its removed edges. -/
noncomputable def rectangleComplementJointEvent
    (hN : Even N) (hM : Even M) (U : Set (FaceVertex N M true))
    (E : Set (Configuration (rectangleComplementGraph hN hM U)))
    (T : Set (RemovedConfiguration (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedEdges hN hM U))) :
    Set (Configuration (rectangleBaseGraph hN hM)) :=
  (embeddedConfigurationRestriction (rectangleComplementGraph hN hM U)
    (rectangleBaseGraph hN hM) (rectangleComplementEmbedding U)
    (rectangleComplementGraph_map_le hN hM U) ⁻¹' E) ∩
      (rectangleComplementRemovedState hN hM U ⁻¹' T)

/-- Free infinite-volume one-arm probability at radius `k` in the rotated
lattice. -/
@[irreducible] noncomputable def rectangleFreeOneArmProbability
    (q : Set.Ici (1 : ℝ)) (k : ℕ) : ℝ :=
  (((Classical.choose (freeBoxLimit_existsUnique (rectangleFKParameters q))
    (oneArmEvent k) : NNReal) : ℝ))

/-- The weighted exploration inequality, with its full rectangle event and
probability content exposed by this definition. -/
@[irreducible] noncomputable def rectangleWeightedExplorationConclusion
    (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
    (U : Set (FaceVertex N M true)) (u : FaceVertex N M true) (huU : u ∉ U)
    (T : Set (RemovedConfiguration (rectangleBaseGraph hN hM)
      (rectangleComplementRemovedEdges hN hM U))) : Prop :=
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
  let R := rectangleComplementRemovedEdges hN hM U
  let out := rectangleComplementRemovedState hN hM U
  let p := law G θ (BoundaryCondition.free ∅)
  let ρ := (((Classical.choose (freeBoxLimit_existsUnique θ)) (oneArmEvent (N / 2 - 1)) : NNReal) : ℝ)
  let S : Set (Configuration G) := (embeddedConfigurationRestriction I G f hIG) ⁻¹' E
  have hf (K) : ∃ C ∈ {C | out C = K}, C ∈ p.support := by
    simpa only [out, rectangleComplementRemovedState, split_second_fiber] using
      frozenStateEvent_support θ (BoundaryCondition.free ∅) R K
  have hmeas : Measurable (embeddedConfigurationRestriction I G f hIG) :=
    measurable_finset_iff.mpr fun e => by
      simpa only [mem_embeddedConfigurationRestriction] using
        measurable_finset_mem (embeddedEdgeEmbedding I G f hIG e)
  have hcond : ∀ K ∈ T, ((p.filter {C | out C = K} (hf K)).toMeasure S).toReal ≤ ρ := by
    intro K hKT
    have hmap := PMF.toMeasure_map_apply
      (f := embeddedConfigurationRestriction I G f hIG)
      (p := p.filter (frozenStateEvent R K) (frozenStateEvent_support θ (BoundaryCondition.free ∅) R K))
      E hmeas (Set.toFinite E).measurableSet
    have hfilter : p.filter {C | out C = K} (hf K) =
        p.filter (frozenStateEvent R K) (frozenStateEvent_support θ (BoundaryCondition.free ∅) R K) := by
      simp only [out, rectangleComplementRemovedState, G, R, split_second_fiber]
    rw [hfilter, ← hmap]
    exact rectangleConditionalRootCrossing_le_freeOneArm hN hM q U u hu huU K (hT K hKT)
  unfold rectangleWeightedExplorationConclusion rectangleBaseEventProbability
    rectangleFreeOneArmProbability
  simpa [PottsDiscontinuity.FK.measure, rectangleComplementJointEvent, p, out, S, E, θ, G, I, f, hIG, ρ] using
    pmf_joint_le_of_fiber_le_on_T p out hf S T ρ hcond

end

end PottsDiscontinuity.TorusLoops
