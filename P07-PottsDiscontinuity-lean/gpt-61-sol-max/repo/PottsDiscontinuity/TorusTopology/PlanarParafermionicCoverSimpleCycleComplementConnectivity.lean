/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenSubgraphOfCycle
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleFilling
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverUnselectedBoundary

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial


open SimpleGraph

/-- The complement carrier keeps the adjoined boundary vertex and all actual
faces outside the named filling. -/
def parafermionicCoverSimpleCycleComplementCarrier {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    Set (Option (ParafermionicCoverFiniteFaceTopIndex n)) :=
  {x | match x with
    | none => True
    | some i => i ∉ S}

def simpleCycleComplementNone {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n)) :
    parafermionicCoverSimpleCycleComplementCarrier S :=
  ⟨none, True.intro⟩

def simpleCycleComplementFace {n : ℕ}
    (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
    (i : ParafermionicCoverFiniteFaceTopIndex n) (hi : i ∉ S) :
    parafermionicCoverSimpleCycleComplementCarrier S :=
  ⟨some i, hi⟩

/-- The actual face adjacency graph induced on the adjoined boundary vertex and
the faces outside a simple-cycle filling is connected. -/
theorem parafermionicCoverSimpleCycleComplementAdjacency_connected {n : ℕ}
    (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ((parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n).induce
      (parafermionicCoverSimpleCycleComplementCarrier
        (parafermionicCoverSimpleCycleFillingSet hn p hp))).Connected := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let V := parafermionicCoverSimpleCycleComplementCarrier S
  
  let C  := (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n).induce V
  let root : V := simpleCycleComplementNone S
  let : Nonempty V := ⟨root⟩
  
  
  
  have hboundary : parafermionicCoverFiniteFaceSetBoundaryGraph S =
      p.toSubgraph.spanningCoe := by
    ext a b
    
    
    have hcycle : s(a,b) ∈ (p.toSubgraph.spanningCoe).edgeSet ↔ s(a,b) ∈ p.edges := by
      rw [SimpleGraph.Subgraph.edgeSet_spanningCoe,
        SimpleGraph.Walk.edgeSet_toSubgraph,
        SimpleGraph.Walk.mem_edgeSet]
    exact ((parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff
              S a b).symm.trans ( (parafermionicCoverSimpleCycleFillingSet_spec hn p hp).right.right  a b)).trans hcycle.symm
  have hroute : ∀ i hiS,
      C.Reachable root (simpleCycleComplementFace S i hiS) := by
    intro i hiS
    let T  :=
      Finset.univ.filter fun j =>
        ∃ hjS : j ∉ S,
          ¬ C.Reachable root (simpleCycleComplementFace S j hjS)
    by_contra hnot
    have hiT : i ∈ T := by
                          grind
    
    have hdisjoint : Disjoint S T := Finset.disjoint_left.mpr fun ⦃j⦄ hjS hjT => Exists.casesOn (Finset.mem_filter.mp hjT).right fun hjNotS h => hjNotS hjS
    
    
    
    
    have hcyclecase := evenSubgraphOfCycle_eq_bot_or_cycle p hp
      (parafermionicCoverFiniteFaceSetBoundaryGraph T)
      (by rw [← hboundary]; exact  parafermionicCoverFiniteFaceUnselectedBoundary_le_selectedBoundary
                                       S T hdisjoint (by
                                                                                     exact fun j hjT hadj => Exists.casesOn (Finset.mem_filter.mp hjT).right fun hjS hjnotreach => hjnotreach (Adj.reachable hadj)) (by
                                                                                                                                   exact fun j hjT k hkS hkT hadj =>
                                                                                                                                           Exists.casesOn (Finset.mem_filter.mp hjT).right fun hjS hjNotReach =>
                                                                                                                                             hjNotReach
                                                                                                                                               (Reachable.trans
                                                                                                                                                 (Decidable.byContradiction fun hknot => hkT (Finset.mem_filter.mpr ⟨Finset.mem_univ k, Exists.intro hkS hknot⟩))
                                                                                                                                                 (Adj.reachable
                                                                                                                                                   (Adj.symm ((parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_some_some_iff j k).mpr hadj))))) ) (parafermionicCoverFiniteFaceSetBoundaryGraph_even_degree T)
    
    rcases hcyclecase with hbot | hwhole
    · exact ((parafermionicCoverFiniteFaceSetBoundaryGraph_ne_bot_iff T).2  ⟨i, hiT⟩ ) hbot
    · 
       
      have hEq : T = S := by
        simpa only [Finset.toList_toFinset] using  parafermionicCoverFiniteFaceChain_toFinset_unique
                                                     T.toList S.toList T.nodup_toList S.nodup_toList  (hwhole.trans hboundary.symm) 
      
      exact (Finset.disjoint_left.mp hdisjoint (by rw [← hEq]; exact hiT) hiT).elim
  refine ⟨?_⟩
  intro x y
  have hx : C.Reachable root x := by
    cases hxv : x.1 with
    | none =>
      have hEq : x = root := by
        grind +locals
      rw [hEq]
    | some i =>
      have hiS : i ∉ S := by
        have hxprop := x.2
        
        rw [hxv] at hxprop
        exact hxprop
      
      have hEq : x = simpleCycleComplementFace S i hiS := Subtype.ext hxv
      simpa [hEq] using  hroute i hiS 
  have hy : C.Reachable root y := by
    cases hyv : y.1 with
    | none =>
      have hEq : y = root := by
        grind +locals
      rw [hEq]
    | some i =>
      have hiS : i ∉ S := by
        have hyprop := y.2
        
        rw [hyv] at hyprop
        exact hyprop
      
      have hEq : y = simpleCycleComplementFace S i hiS := Subtype.ext hyv
      simpa [hEq] using  hroute i hiS 
  exact hx.symm.trans hy

end PottsDiscontinuity.TorusTopology.Planar.Medial
