module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.TorusExploration.ClusterComplementFreeLaw
public import PottsDiscontinuity.TorusExploration.DistinctConnections
public import PottsDiscontinuity.TorusExploration.FiberAveraging
public import PottsDiscontinuity.TorusExploration.FiniteBoxComparison
public import PottsDiscontinuity.TorusExploration.InducedConnectivity

/-! A genuine conditional exploration bound after revealing complete clusters. -/

@[expose] public section

namespace PottsDiscontinuity.TorusExploration
open FK FK.FiniteProbability
variable {V : Type*} [Finite V] (G : SimpleGraph V)
noncomputable section
open scoped Classical
local instance conditionalConnectionEdgeFintype : Fintype G.edgeSet := Fintype.ofFinite _

lemma expectation_le_on_support {α : Type*} [Fintype α] (p : PMF α) (F H : α → ℝ)
    (h : ∀ a, a ∈ p.support → F a ≤ H a) : expectation p F ≤ expectation p H := by
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : p a=0
  · simp [ha]
  · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg

lemma fkLaw_full_support (θ : Parameters) (ξ : BoundaryCondition V) (A : Configuration G) :
    A ∈ (law G θ ξ).support := by rw [law_support]; trivial

lemma clusterRecordConditional_eq (θ : Parameters) (S : Finset V) (A : Configuration G) :
    recordConditional (law G θ (BoundaryCondition.free ∅))
      (fkLaw_full_support G θ _) (clusterRecord G S) A =
    (law G θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent G (actualMultiClusterReveal G S) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent G (actualMultiClusterReveal G S)
          (actualMultiClusterReveal_consistent S) A]
        exact frozenStateEvent_support θ (BoundaryCondition.free ∅)
          (actualMultiClusterReveal G S A) (revealRecordConfiguration G (actualMultiClusterReveal G S) A)) := by
  have he : {B | clusterRecord G S B=clusterRecord G S A} =
      revealRecordEvent G (actualMultiClusterReveal G S) A :=
    Set.ext (fun B => clusterRecord_eq_iff G S A B)
  unfold recordConditional
  congr 1

/-- An actual open connection from a prescribed vertex to a target set. -/
def rootedConnection (u : V) (K : Set V) : Set (Configuration G) :=
  {A | ∃ v ∈ K, ActualConnected G A u v}

/-- A rooted connection in a cluster disjoint from all previously exposed seeds. -/
def freshConnection (S : Finset V) (u : V) (K : Set V) : Set (Configuration G) :=
  {A | u ∈ actualMultiClusterComplementSet G S A ∧ A ∈ rootedConnection G u K}

/-- After exposing clusters, the next fresh connection is controlled by the
free law on the unexplored graph. The target may be a set or a singleton. -/
theorem freshConnection_conditional_le (θ : Parameters) (S : Finset V) (A : Configuration G)
    (u : V) (K : Set V) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ h : u ∈ actualMultiClusterComplementSet G S A,
      (measure (G.induce (actualMultiClusterComplementSet G S A)) θ (BoundaryCondition.free ∅)
        (rootedConnection _ ⟨u, h⟩ (Subtype.val ⁻¹' K))).toReal ≤ c) :
    expectation (recordConditional (law G θ (BoundaryCondition.free ∅))
      (fkLaw_full_support G θ _) (clusterRecord G S) A)
      ((freshConnection G S u K).indicator fun _ => (1 : ℝ)) ≤ c := by
  let T := actualMultiClusterComplementSet G S A
  let P := recordConditional (law G θ (BoundaryCondition.free ∅))
    (fkLaw_full_support G θ _) (clusterRecord G S) A
  have hout (B : Configuration G) (hB : B ∈ P.support) :
      actualMultiClusterComplementSet G S B = T := by
    have hr := ((clusterRecord_eq_iff G S A B).1 ((PMF.mem_support_filter_iff _).1 hB).1).2
    exact Set.ext fun v => not_congr (actualMultiClusterConnected_iff_of_reveal_agreement S A B hr v)
  by_cases hu : u ∈ T
  · let I := G.induce T
    let R := embeddedConfigurationRestriction I G (inducedVertexEmbedding T) (inducedVertexGraph_le G T)
    let E := rootedConnection I (⟨u, hu⟩ : T) (Subtype.val ⁻¹' K)
    let : Fintype I.edgeSet := Fintype.ofFinite _
    have hm : P.map R = law I θ (BoundaryCondition.free ∅) := by
      rw [show P = _ from clusterRecordConditional_eq G θ S A]
      exact law_filter_actualMultiClusterRecord_map_complement_free θ S A
    calc
      _ ≤ expectation P (fun B => E.indicator (fun _ => (1 : ℝ)) (R B)) := by
        apply expectation_le_on_support
        intro B hB
        by_cases hb : B ∈ freshConnection G S u K
        · have hb' := hb
          obtain ⟨_, v, hv, hreach⟩ := hb'
          have hstay (x y : V) (hx : x ∈ T) (hxy : ActualConnected G B x y) : y ∈ T := by
            rw [← hout B hB] at hx ⊢
            exact fun ⟨s, hs, hsy⟩ => hx ⟨s, hs, hsy.trans hxy.symm⟩
          have hv' : R B ∈ E := ⟨⟨v, hstay u v hu hreach⟩, hv,
            (actualConnected_inducedRestriction G T B (fun x hx y hxy => hstay x y hx hxy.reachable) _ _).2 hreach⟩
          simp [hb, hv']
        · rw [Set.indicator_of_notMem hb]
          exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
      _ ≤ c := by rw [← expectation_map, hm, ← fk_measureReal_eq_expectation]; exact hc hu
  · refine le_trans ?_ hc0
    rw [← expectation_const P 0]
    apply expectation_le_on_support
    intro B hB
    have hn : B ∉ freshConnection G S u K := fun h => hu (hout B hB ▸ h.1)
    simp [hn]

theorem nextDistinct_conditional_le (θ : Parameters) (x y : ℕ → V) (j : ℕ)
    (A : Configuration G) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ (hx : x j ∈ actualMultiClusterComplementSet G (prefixSeeds x j) A)
      (hy : y j ∈ actualMultiClusterComplementSet G (prefixSeeds x j) A),
      (measure (G.induce (actualMultiClusterComplementSet G (prefixSeeds x j) A)) θ
        (BoundaryCondition.free ∅) (connectivityEvent _ ⟨x j,hx⟩ ⟨y j,hy⟩)).toReal ≤ c) :
    expectation (recordConditional (law G θ (BoundaryCondition.free ∅))
      (fkLaw_full_support G θ _) (clusterRecord G (prefixSeeds x j)) A)
      ((nextDistinctConnection G x y j).indicator fun _ => (1 : ℝ)) ≤ c := by
  have he : nextDistinctConnection G x y j = freshConnection G (prefixSeeds x j) (x j) {y j} := by
    ext B
    simp only [nextDistinctConnection, freshConnection, rootedConnection, Set.mem_ofPred_eq,
      Set.mem_singleton_iff, actualMultiClusterComplementSet, actualMultiClusterConnected,
      prefixSeeds, Finset.mem_image, Finset.mem_range]
    grind
  rw [he]
  apply freshConnection_conditional_le G θ _ A _ _ c hc0
  let T := actualMultiClusterComplementSet G (prefixSeeds x j) A
  intro hx
  by_cases hy : y j ∈ T
  · have hE : rootedConnection (G.induce T) ⟨x j, hx⟩ (Subtype.val ⁻¹' {y j}) =
        connectivityEvent _ ⟨x j, hx⟩ ⟨y j, hy⟩ := by
      ext B
      change (∃ z : T, z.val = y j ∧ ActualConnected (G.induce T) B ⟨x j, hx⟩ z) ↔
        ActualConnected (G.induce T) B ⟨x j, hx⟩ ⟨y j, hy⟩
      constructor
      · rintro ⟨z, hz, hr⟩
        exact (Subtype.ext hz : z = ⟨y j, hy⟩) ▸ hr
      · exact fun h => ⟨⟨y j, hy⟩, rfl, h⟩
    rw [hE]
    exact hc hx hy
  · have hE : rootedConnection (G.induce T) ⟨x j, hx⟩ (Subtype.val ⁻¹' {y j}) = ∅ := by
      ext B
      constructor
      · rintro ⟨z, hz, _⟩
        exact (hy ((Set.mem_singleton_iff.mp hz) ▸ z.property)).elim
      · simp
    rw [hE]
    simpa using hc0

end
end PottsDiscontinuity.TorusExploration
