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
  · simp [*]
  · exact mul_le_mul_of_nonneg_left (h a ha) ENNReal.toReal_nonneg

variable (θ : Parameters) (ξ : BoundaryCondition V) (S : Finset V) (x y : ℕ → V) (j : ℕ)
    (A : Configuration G)

lemma fkLaw_full_support :
    A ∈ (law G θ ξ).support := by rw [law_support]; trivial

lemma clusterRecordConditional_eq :
    recordConditional (p := (law G θ (BoundaryCondition.free ∅)))
      (fkLaw_full_support G θ _) (clusterRecord G S) A =
    (law G θ (BoundaryCondition.free ∅)).filter
      (revealRecordEvent G (actualMultiClusterReveal G S) A)
      (by
        rw [revealRecordEvent_eq_frozenStateEvent G
          (actualMultiClusterReveal_consistent S) A]
        solve_by_elim [frozenStateEvent_support]) := by
  have he :=
    Set.ext (fun B => clusterRecord_eq_iff G S A B)
  unfold recordConditional
  congr 1

/-- Conditioning on the full preceding cluster records bounds the next
*distinct* prescribed connection by its free-law probability on the induced
unexplored graph. The geometric estimate is supplied separately. -/
theorem nextDistinct_conditional_le (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ hx
      hy,
      (measure (G.induce (actualMultiClusterComplementSet (G := G) (prefixSeeds x j) A)) θ
        (BoundaryCondition.free ∅) (connectivityEvent _ ⟨x j,hx⟩ ⟨y j,hy⟩)).toReal ≤ c) :
    expectation (recordConditional (p := (law G θ (BoundaryCondition.free ∅)))
      (fkLaw_full_support G θ _) (clusterRecord G (prefixSeeds x j)) A)
      ((nextDistinctConnection G x y j).indicator fun _ => 1) ≤ c := by
  let S := prefixSeeds x j
  let T := actualMultiClusterComplementSet S A
  let P := recordConditional (p := (law G θ (BoundaryCondition.free ∅)))
    (fkLaw_full_support G θ _) (clusterRecord G S) A
  have hrec (B : Configuration G) (hB : B ∈ P.support) := (PMF.mem_support_filter_iff _).1 hB |>.1
  have hout (B : Configuration G) (hB : B ∈ P.support) (v : V) :
      v ∈ actualMultiClusterComplementSet S B ↔ v ∈ T := not_congr (actualMultiClusterConnected_iff_of_reveal_agreement S A B ((clusterRecord_eq_iff G S A B).mp (hrec B hB)).right v)
  by_cases hx : x j ∈ T
  · by_cases hy : y j ∈ T
    · let u : T := ⟨x j,hx⟩
      let v : T := ⟨y j,hy⟩
      let H := G.induce T
      let R := embeddedConfigurationRestriction H G _ (inducedVertexGraph_le G T)
      have hm : P.map R=law H θ (BoundaryCondition.free ∅) := by
        rw [show P = _ from clusterRecordConditional_eq G θ S A]
        exact law_filter_actualMultiClusterRecord_map_complement_free θ S A
      have hstep : expectation P ((nextDistinctConnection G x y j).indicator fun _ => 1) ≤
          expectation P (fun B => (connectivityEvent H u v).indicator (fun _ => 1) (R B)) := by
        apply expectation_le_on_support
        intro B hB
        by_cases hnext : B ∈ nextDistinctConnection G x y j
        · have hconn :=
            (actualConnected_inducedRestriction G T B (by
              intro a ha b hab hb
              have haB := (hout B hB a).2 ha
              have hbT : b ∉ T := fun hn => hn hb
              have hbB := (hout B hB b).not.2 hbT
              obtain ⟨s,hs,hconn⟩ := Classical.not_not.1 hbB
              exact haB ⟨s,hs,hconn.trans hab.symm.reachable⟩) u v).2 hnext.1
          have hconnE : R B ∈ connectivityEvent H u v := hconn
          simp [*]
        · simp only [Set.indicator_of_notMem hnext]
          by_cases hh : R B ∈ connectivityEvent H u v <;> simp [hh]
      refine hstep.trans ?_
      rw [← expectation_map,hm,← fk_measureReal_eq_expectation]
      exact hc hx hy
    · have hz : expectation P ((nextDistinctConnection G x y j).indicator fun _ => 1)=0 := by
        rw [← expectation_const P 0]
        apply expectation_congr_on_support
        intro B hB
        have hn : B ∉ nextDistinctConnection G x y j := by
          intro hh
          exact hy ((hout B hB _).1 (nextDistinctConnection_outside G x y j B hh).2)
        simp [hn]
      grind
  · have hz : expectation P ((nextDistinctConnection G x y j).indicator fun _ => 1)=0 := by
      rw [← expectation_const P 0]
      apply expectation_congr_on_support
      intro B hB
      have hn : B ∉ nextDistinctConnection G x y j := by
        intro hh
        exact hx ((hout B hB _).1 (nextDistinctConnection_outside G x y j B hh).1)
      simp [hn]
    grind

end
end PottsDiscontinuity.TorusExploration
