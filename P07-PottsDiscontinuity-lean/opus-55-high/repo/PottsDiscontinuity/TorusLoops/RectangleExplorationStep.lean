module

public import PottsDiscontinuity.TorusLoops.RectangleClusterBoundary
public import PottsDiscontinuity.TorusLoops.RectangleRootCrossings

/-!
# One-step bound for exploration outside a revealed cluster

Freezing all edges not in the induced complement graph, when the frozen open
edges lie within the explored region, leaves a free FK boundary on the
complement. An increasing crossing in that complement is bounded by the
whole-rectangle rooted crossing, hence by the free one-arm probability.
-/

@[expose] public section

namespace PottsDiscontinuity.TorusLoops

open MeasureTheory
open PottsDiscontinuity.Torus
open PottsDiscontinuity.CorrLength
open PottsDiscontinuity.Zhang
open PottsDiscontinuity.FK

noncomputable section

local instance explorationGenericEdgeFintype
    {V : Type*} [Finite V] {G : SimpleGraph V} : Fintype G.edgeSet :=
  Fintype.ofFinite _


variable {N M : ℕ}

/-- Vertices in the complement of an explored set of rectangle vertices. -/
abbrev RectangleComplementVertex (N M : ℕ) (U : Set (FaceVertex N M true)) :=
  {x : FaceVertex N M true // x ∉ U}

/-- The subgraph induced by the vertices outside the explored region. -/
def rectangleComplementGraph (hN : Even N) (hM : Even M)
    (U : Set (FaceVertex N M true)) : SimpleGraph (RectangleComplementVertex N M U) :=
  (rectangleBaseGraph hN hM).induce {x | x ∉ U}

/-- The natural inclusion of the unexplored vertices in the rectangle. -/
def rectangleComplementEmbedding (U : Set (FaceVertex N M true)) :
    RectangleComplementVertex N M U ↪ FaceVertex N M true :=
  Function.Embedding.subtype _

section
variable (hN : Even N) (hM : Even M) (U : Set (FaceVertex N M true))
theorem rectangleComplementGraph_map_le  :
    (rectangleComplementGraph hN hM U).map (rectangleComplementEmbedding U) ≤
      rectangleBaseGraph hN hM := by
  intro x y hxy
  rw [SimpleGraph.map_adj] at hxy
  rcases hxy with ⟨a, b, hab, rfl, rfl⟩
  tauto

/-- A rooted horizontal crossing event in the induced graph outside `U`. -/
def rectangleComplementRootCrossingEvent (u : FaceVertex N M true) (huU : u ∉ U) :
    Set (Configuration (rectangleComplementGraph hN hM U)) :=
  {C | ∃ v : RectangleComplementVertex N M U,
    v.val.val.1.val + 1 = N ∧
    ActualConnected (rectangleComplementGraph hN hM U) C ⟨u, huU⟩ v}

theorem rectangleComplementRootCrossingEvent_isUpperSet
    (u : FaceVertex N M true) (huU : u ∉ U) :
    IsUpperSet (rectangleComplementRootCrossingEvent hN hM U u huU) := by
  intro A B hAB hA
  rcases hA with ⟨v, hv, hconn⟩
  exact ⟨v, hv, actualConnected_mono hAB hconn⟩
end

section
variable (hN : Even N) (hM : Even M) (q : Set.Ici (1 : ℝ))
/-- Conditional one-step exploration bound. The exact outside state `K` may
have arbitrary closed edges; its open edges must stay inside the explored set
`U`. The conditional law on the induced complement then has free boundary,
and the probability that the next left-boundary root crosses is at most the
free one-arm probability. -/
theorem rectangleConditionalRootCrossing_le_freeOneArm
    (U : Set (FaceVertex N M true)) (u : FaceVertex N M true)
    (hu : u.val.1.val = 0) (huU : u ∉ U)
    (K : RemovedConfiguration (rectangleBaseGraph hN hM)
      (subgraphRemovedEdges
        ((rectangleComplementGraph hN hM U).map (rectangleComplementEmbedding U))
        (rectangleBaseGraph hN hM)))
    (hK : ∀ ⦃x y : FaceVertex N M true⦄,
      (openGraph (rectangleBaseGraph hN hM) K.val).Adj x y → x ∈ U ∧ y ∈ U) :
    (PMF.toMeasure (((law (rectangleBaseGraph hN hM)
      (rectangleFKParameters q) (BoundaryCondition.free ∅)).filter
        (frozenStateEvent
          (subgraphRemovedEdges
            ((rectangleComplementGraph hN hM U).map (rectangleComplementEmbedding U))
            (rectangleBaseGraph hN hM)) K)
        (frozenStateEvent_support (rectangleFKParameters q)
          (BoundaryCondition.free ∅)
          (subgraphRemovedEdges
            ((rectangleComplementGraph hN hM U).map (rectangleComplementEmbedding U))
            (rectangleBaseGraph hN hM)) K)).map
        (embeddedConfigurationRestriction
          (rectangleComplementGraph hN hM U) (rectangleBaseGraph hN hM)
          (rectangleComplementEmbedding U)
          (rectangleComplementGraph_map_le hN hM U)))
      (rectangleComplementRootCrossingEvent hN hM U u huU)).toReal ≤
      (((Classical.choose (freeBoxLimit_existsUnique
        (rectangleFKParameters q))) (oneArmEvent (N / 2 - 1)) : NNReal) : ℝ) := by
  let G := rectangleBaseGraph hN hM
  let I := rectangleComplementGraph hN hM U
  let f := rectangleComplementEmbedding U
  let hIG := rectangleComplementGraph_map_le hN hM U
  let θ := rectangleFKParameters q
  let E := rectangleComplementRootCrossingEvent hN hM U u huU
  let T := rectangleRootCrossingEvent hN hM u
  let R := subgraphRemovedEdges (I.map f) G
  have hE : IsUpperSet E := by
    grind [rectangleComplementRootCrossingEvent_isUpperSet]
  have hpart :
      (isolatedExtensionPullbackBoundary f (frozenBoundary
        (BoundaryCondition.free ∅) K.val)).partition ≤
        (BoundaryCondition.free ∅).partition :=
    isolatedExtensionPullbackFrozenFree_of_openEdges_inside
      f hIG K U hK (fun x => x.property)
  have hconditional := filteredConditionalEmbeddedEvent_measure_le_boundary
    I G f hIG θ (BoundaryCondition.free ∅) K (BoundaryCondition.free ∅)
    hpart E hE
  have hTcontains (A : Configuration G) :
      embeddedConfigurationRestriction I G f hIG A ∈ E → A ∈ T := by
    intro hA
    rcases hA with ⟨v, hv, hconn⟩
    have hconnA :=
      actualConnected_mono (embeddedConfigurationEmbedding_restriction_subset I G f hIG A) (actualConnected_embeddedConfigurationEmbedding I G f hIG _ _ _ hconn)
    have hfu : f ⟨u, huU⟩ = u := rfl
    have hconnA' : ActualConnected G A u (f v) := by
      grind
    exact ⟨f v, hv, hconnA'⟩
  have hfreeCompare : (measure I θ (BoundaryCondition.free ∅) E).toReal ≤
      (measure G θ (BoundaryCondition.free ∅) T).toReal := by
    rw [fkLaw_measure_toReal_eq_expectation θ (BoundaryCondition.free ∅) E,
      fkLaw_measure_toReal_eq_expectation θ (BoundaryCondition.free ∅) T]
    let ind := E.indicator (fun _ => (1 : ℝ))
    have hind0 : ∀ A, 0 ≤ ind A := by
      intro A
      by_cases hA : A ∈ E <;> simp [ind, hA]
    have hind : Monotone ind := by
      intro A B hAB
      by_cases hA : A ∈ E
      · simp [ind, hA, (hE hAB hA)]
      · simp only [ind, Set.indicator_of_notMem hA]
        grind
    have hcmp := embedded_free_marginal_comparison I G f hIG θ ∅ ∅ ind hind0 hind
    rw [FiniteProbability.expectation_map] at hcmp
    have hpoint (A : Configuration G) :
        ind (embeddedConfigurationRestriction I G f hIG A) ≤
          T.indicator (fun _ => (1 : ℝ)) A := by
      by_cases hA : embeddedConfigurationRestriction I G f hIG A ∈ E
      · grind [Set.indicator]
      · by_cases hTA : A ∈ T <;> simp [ind, Set.indicator, hA, hTA]
    exact hcmp.trans (FiniteProbability.expectation_mono _ _ _ hpoint)
  have hroot : (measure G θ (BoundaryCondition.free ∅) T).toReal ≤
      (((Classical.choose (freeBoxLimit_existsUnique θ))
        (oneArmEvent (N / 2 - 1)) : NNReal) : ℝ) := by
    rw [← rectangleFKEventProbability_eq_measure hN hM q T]
    exact rectangleFKProbability_rootCrossing_le_freeOneArm hN hM u hu q
  simpa [G, I, f, hIG, θ, E, T, R] using hconditional.trans (hfreeCompare.trans hroot)
end

end
end PottsDiscontinuity.TorusLoops
