module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.Homotopy.Path
public import PottsDiscontinuity.Duality.CircuitEnclosure
public import PottsDiscontinuity.Duality.WholePlaneDualConfiguration
public import PottsDiscontinuity.RCInfinite.GraphModification

/-! If there is no infinite primal cluster, closed dual circuits force
connections from arbitrarily distant points of a fixed ray to the opposite half-plane. -/

public section

namespace PottsDiscontinuity.Duality
open FK FK.Medial
noncomputable section

theorem rayStep_ne_zero_coordinates (v u w : LatticeVertex) (h : squareLattice.Adj u w)
    (hn : rayStep v u w ≠ 0) :
    v.1 ≤ u.1 ∧ u.1 = w.1 ∧ (u.2 = v.2-1 ∨ u.2 = v.2) := by
  have ha := (squareLattice_adj_iff _ _).1 h
  grind [rayStep]

theorem rayIndex_ne_zero_rightWitness (v : LatticeVertex) {u w : LatticeVertex}
    (p : squareLattice.Walk u w) (hn : rayIndex v p ≠ 0) :
    ∃ t ∈ p.support, v.1 ≤ t.1 ∧ (t.2 = v.2-1 ∨ t.2 = v.2) := by
  induction p with
  | nil => tauto
  | @cons u z w h p ih =>
    grind [rayStep, rayIndex, rayStep_ne_zero_coordinates]

theorem rayIndex_ne_zero_leftWitness {z : LatticeVertex} (p : squareLattice.Walk z z)
    (hn : rayIndex (0,0) p ≠ 0) : ∃ t ∈ p.support, t.1 < 0 := by
  by_contra! hall
  have heq := rayIndex_left_telescope (0,0) p hall
  omega

theorem reachable_support_of_edge_relation {G : SimpleGraph LatticeVertex}
    {u w : LatticeVertex} (p : squareLattice.Walk u w)
    (hG : ∀ a b, s(a,b) ∈ p.edges → G.Adj a b) :
    ∀ t ∈ p.support, G.Reachable u t := by
  induction p with
  | nil => simp
  | @cons u z w h p ih =>
    intro t ht
    simp at ht
    rcases ht with rfl | ht
    · rfl
    · have hh := hG u z (by simp)
      have htail : ∀ a b, s(a,b) ∈ p.edges → G.Adj a b := by
        tauto
      exact hh.reachable.trans (ih htail t ht)

theorem closedDualGraph_opening_le (F : Finset squareLattice.edgeSet) (ω : LatticeConfiguration) :
    wholePlaneClosedDualGraph (RCInfinite.setEdges F (fun _ => true) ω) ≤
      wholePlaneClosedDualGraph ω := by
  intro u w huw
  obtain ⟨b,hb,hdir⟩ := (wholePlaneClosedDualGraph_adj_iff _ _ _).1 huw
  apply (wholePlaneClosedDualGraph_adj_iff _ _ _).2
  change (if latticeBondEdge b ∈ F then true else ω (latticeBondEdge b)) = false at hb
  aesop

/-- Absence of infinite clusters forces arbitrarily long actual open dual
connections from one of the two adjacent axis rows to the negative half-plane. -/
theorem no_infinite_cluster_implies_opposite_connections (ω : LatticeConfiguration)
    (hno : ω ∉ existsInfiniteCluster) (R : ℕ) :
    ∃ k : ℕ, ∃ j : Fin 2, ∃ w : LatticeVertex, R ≤ k ∧ w.1 < 0 ∧
      wholePlaneDualConfigurationHomeomorph ω ∈ connectionEvent ((k : ℤ),-(j.val : ℤ)) w := by
  obtain ⟨F,hF⟩ := RCInfinite.exists_finite_opening_connects 2 ![(0,0),((R : ℤ),0)]
  let η := RCInfinite.setEdges F (fun _ => true) ω
  have hf : (cluster η 0).Finite := by
    by_contra hn
    obtain ⟨t,_,ht⟩ := RCInfinite.opening_infinite_component_contains_old F ω 0 hn
    tauto
  obtain ⟨z,p,hp,hclosed,hidx,_⟩ := finite_cluster_has_surrounding_closedDual_circuit η 0 hf
  have hr : (rcInfiniteOpenGraph η).Reachable 0 ((R : ℤ),0) :=
    hF ω 0 1
  have hRidx : rayIndex ((R : ℤ),0) p ≠ 0 := by
    rw [← rayIndex_eq_of_avoidance_reachable p
      (hr.mono (openGraph_le_circuitAvoidance η p hclosed))]
    omega
  obtain ⟨u,hu,hux,huy⟩ := rayIndex_ne_zero_rightWitness ((R : ℤ),0) p hRidx
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
  have hk : (k : ℤ) = u.1 := by omega
  have hRk : R ≤ k := by omega
  rcases huy with huy | huy
  · refine ⟨k,1,w,hRk,hwx,?_⟩
    have heq : ((k : ℤ),-((1 : Fin 2).val : ℤ)) = u := by
      ext <;> simp only [hk,Fin.val_one,Int.natCast_one]; omega
    change (rcInfiniteOpenGraph (wholePlaneDualConfigurationHomeomorph ω)).Reachable _ w
    simp_all
  · refine ⟨k,0,w,hRk,hwx,?_⟩
    have heq : ((k : ℤ),-((0 : Fin 2).val : ℤ)) = u := by
      ext <;> simp only [hk,Fin.val_zero,Int.natCast_zero,neg_zero]
      omega
    change (rcInfiniteOpenGraph (wholePlaneDualConfigurationHomeomorph ω)).Reachable _ w
    simp_all

end
end PottsDiscontinuity.Duality
