module
public import Mathlib

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.CircuitEnclosure
public import PottsDiscontinuity.Duality.WholePlaneDualConfiguration
public import PottsDiscontinuity.RCInfinite.GraphModification

/-! If there is no infinite primal cluster, closed dual circuits force
connections from arbitrarily distant points of a fixed ray to the opposite half-plane. -/

@[expose] public section

namespace PottsDiscontinuity.Duality
open FK FK.Medial
noncomputable section

lemma rayStep_ne_zero_coordinates (v u w : LatticeVertex) (h : squareLattice.Adj u w)
    (hn : rayStep v u w ≠ 0) :
    v.1 ≤ u.1 ∧ u.1 = w.1 ∧ (u.2 = v.2-1 ∨ u.2 = v.2) := by
  
  
  
  
  
  rcases ((squareLattice_adj_iff _ _).1 h) with ⟨h | h, hy⟩ | ⟨hx, h | h⟩ <;>
    dsimp [rayStep] at hn <;> split_ifs at hn <;> norm_num at hn <;> omega

lemma rayIndex_ne_zero_rightWitness (v : LatticeVertex) {u w : LatticeVertex}
    (p : squareLattice.Walk u w) (hn : rayIndex v p ≠ 0) :
    ∃ t ∈ p.support, v.1 ≤ t.1 ∧ (t.2 = v.2-1 ∨ t.2 = v.2) := by
  induction p with
  | nil => exact (hn rfl).elim
  | @cons u z w h p ih =>
    grind [rayStep, rayIndex, rayStep_ne_zero_coordinates]

lemma rayIndex_ne_zero_leftWitness {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hn : rayIndex (0,0) p ≠ 0) : ∃ t ∈ p.support, t.1 < 0 := by
  by_contra! hall
  
  have heq := rayIndex_left_telescope (0,0) p  hall 
  simp_all

lemma reachable_support_of_edge_relation {G : SimpleGraph LatticeVertex}
    {u w : LatticeVertex} (p : squareLattice.Walk u w)
    (hG : ∀ a b, s(a,b) ∈ p.edges → G.Adj a b) :
    ∀ t ∈ p.support, G.Reachable u t := by
  induction p with
  | nil => simp_all
  | @cons u z w h p ih =>
    intro t ht
    simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact .refl _
    · 
      
      exact (hG u z (by simp)).reachable.trans (ih (by
                                      simp_all) t ht)

lemma closedDualGraph_opening_le (F : Finset squareLattice.edgeSet) (ω : LatticeConfiguration) :
    wholePlaneClosedDualGraph (RCInfinite.setEdges F (fun _ => true) ω) ≤
      wholePlaneClosedDualGraph ω := by
  intro u w huw
  obtain ⟨b,hb,hdir⟩ := (wholePlaneClosedDualGraph_adj_iff _ _ _).1 huw
  
  refine ⟨b,?_,hdir⟩
  change (if latticeBondEdge b ∈ F then true else ω (latticeBondEdge b)) = false at hb
  aesop

/-- Absence of infinite clusters forces arbitrarily long actual open dual
connections from one of the two adjacent axis rows to the negative half-plane. -/
theorem no_infinite_cluster_implies_opposite_connections (ω : LatticeConfiguration)
    (hno : ω ∉ existsInfiniteCluster) (R : ℕ) :
    ∃ k : ℕ, ∃ j : Fin 2, ∃ w : LatticeVertex, R ≤ k ∧ w.1 < 0 ∧
      wholePlaneDualConfigurationHomeomorph ω ∈ connectionEvent ((k : ℤ),-(j.val : ℤ)) w := by
  
  obtain ⟨F,hF⟩ := RCInfinite.exists_finite_opening_connects 2 ![(0,0),(R,0)]
  let η := RCInfinite.setEdges F (fun _ => true) ω
  
  obtain ⟨z,p,hp,hclosed,hidx,_⟩ := finite_cluster_has_surrounding_closedDual_circuit η 0 (by
                                                                                             by_contra hn
                                                                                             have hi  := hn
                                                                                             obtain ⟨t,_,ht⟩ := RCInfinite.opening_infinite_component_contains_old F ω 0 hi
                                                                                             exact hno ⟨t,ht⟩)
  have hr : (rcInfiniteOpenGraph η).Reachable 0 (R,0) := hF ω 0 1
  
  obtain ⟨u,hu,hux,huy⟩ := rayIndex_ne_zero_rightWitness (R,0) p (by
                                                                    rw [← rayIndex_eq_of_avoidance_reachable p
                                                                      (hr.mono (openGraph_le_circuitAvoidance η p hclosed))]
                                                                    exact hidx)
  obtain ⟨w,hw,hwx⟩ := rayIndex_ne_zero_leftWitness p hidx
  have hc : ∀ a b, s(a,b) ∈ p.edges → (rcInfiniteOpenGraph
      (wholePlaneDualConfigurationHomeomorph ω)).Adj a b := by
    intro a b he
    rw [← wholePlaneOpenPrimalGraph_eq_rcInfiniteOpenGraph,
      wholePlaneOpenPrimalGraph_dualConfiguration_eq]
    exact closedDualGraph_opening_le F ω (hclosed a b he)
  have hconn := (reachable_support_of_edge_relation p hc u hu).symm.trans
    (reachable_support_of_edge_relation p hc w hw)
  let k := u.1.toNat
  have hk :  k  = u.1 := by  omega
  have hRk : R ≤ k := by  omega
  rcases huy with huy | huy
  · refine ⟨k,1,w,hRk,hwx,?_⟩
    
    
    rw [(by
           aesop : ((k : ℤ),-((1 : Fin 2).val : ℤ)) = u)]
    exact hconn
  · refine ⟨k,0,w,hRk,hwx,?_⟩
    
    
    rw [(by
           aesop : ((k : ℤ),-((0 : Fin 2).val : ℤ)) = u)]
    exact hconn

end
end PottsDiscontinuity.Duality
