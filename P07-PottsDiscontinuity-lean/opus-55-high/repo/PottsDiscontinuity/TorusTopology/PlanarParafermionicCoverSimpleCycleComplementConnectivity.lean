/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic
public import PottsDiscontinuity.TorusTopology.PlanarFiniteEvenSubgraphOfCycle
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleFilling
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverUnselectedBoundary

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

section
variable {n : ℕ} (S : Finset (ParafermionicCoverFiniteFaceTopIndex n))
/-- The complement carrier keeps the adjoined boundary vertex and all actual
faces outside the named filling. -/
def parafermionicCoverSimpleCycleComplementCarrier  :
    Set (Option (ParafermionicCoverFiniteFaceTopIndex n)) :=
  {x | match x with
    | none => True
    | some i => i ∉ S}

def simpleCycleComplementNone  :
    parafermionicCoverSimpleCycleComplementCarrier S :=
  ⟨none, by tauto⟩

def simpleCycleComplementFace (i : ParafermionicCoverFiniteFaceTopIndex n) (hi : i ∉ S) :
    parafermionicCoverSimpleCycleComplementCarrier S :=
  ⟨some i, by tauto⟩
end

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
  let G :=
    parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph n
  let C := G.induce V
  let root := simpleCycleComplementNone S
  let : Nonempty V := by tauto
  have hfill := parafermionicCoverSimpleCycleFillingSet_spec hn p hp
  have hboundary : parafermionicCoverFiniteFaceSetBoundaryGraph S =
      p.toSubgraph.spanningCoe := by
    ext a b
    rw [← (parafermionicCoverFiniteFaceSetBoundaryGraph S).mem_edgeSet,
      ← (p.toSubgraph.spanningCoe).mem_edgeSet]
    have hBS := parafermionicCoverFiniteFaceSetBoundaryGraph_coefficient_ne_zero_iff
      S a b
    have hcycle : s(a,b) ∈ (p.toSubgraph.spanningCoe).edgeSet ↔ s(a,b) ∈ p.edges := by
      simp
    grind
  have hroute : ∀ (i : ParafermionicCoverFiniteFaceTopIndex n) (hiS : i ∉ S),
      C.Reachable root (simpleCycleComplementFace S i hiS) := by
    intro i hiS
    let T :=
      Finset.univ.filter fun j =>
        ∃ hjS : j ∉ S,
          ¬ C.Reachable root (simpleCycleComplementFace S j hjS)
    by_contra hnot
    have hiT : i ∈ T :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hiS,hnot⟩⟩
    have hTnonempty : T.Nonempty := ⟨i, hiT⟩
    have hdisjoint : Disjoint S T := by
      apply Finset.disjoint_left.mpr
      intro j hjS hjT
      obtain ⟨hjNotS,_⟩ := (Finset.mem_filter.mp hjT).2
      exact hjNotS hjS
    have hnoExposed : ∀ j ∈ T,
        ¬ G.Adj none (some j) := by
      intro j hjT hadj
      obtain ⟨hjS,hjnotreach⟩ := (Finset.mem_filter.mp hjT).2
      have hadjC : C.Adj root (simpleCycleComplementFace S j hjS) := by
        change G.Adj none (some j)
        omega
      exact hjnotreach hadjC.reachable
    have hnoCross : ∀ j ∈ T, ∀ k, k ∉ S → k ∉ T →
        ¬ (parafermionicCoverFiniteFaceAdjacencyGraph n).Adj j k := by
      intro j hjT k hkS hkT hadj
      obtain ⟨hjS,hjNotReach⟩ := (Finset.mem_filter.mp hjT).2
      have hkReach : C.Reachable root (simpleCycleComplementFace S k hkS) := by
        by_contra hknot
        exact hkT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hkS,hknot⟩⟩)
      have hadjOption :=
        (parafermionicCoverFiniteFaceAdjacencyWithBoundaryGraph_adj_some_some_iff j k).2
          (show (parafermionicCoverFiniteFaceAdjacencyGraph n).Adj j k from hadj)
      have hadjC : C.Adj (simpleCycleComplementFace S j hjS)
          (simpleCycleComplementFace S k hkS) := by
        change G.Adj (some j) (some k)
        omega
      exact hjNotReach (hkReach.trans hadjC.symm.reachable)
    have hsub :=
      parafermionicCoverFiniteFaceUnselectedBoundary_le_selectedBoundary
        S T hdisjoint hnoExposed hnoCross
    have hcyclecase := evenSubgraphOfCycle_eq_bot_or_cycle p hp
      (parafermionicCoverFiniteFaceSetBoundaryGraph T)
      (by rw [← hboundary]; omega) (parafermionicCoverFiniteFaceSetBoundaryGraph_even_degree T)
    rcases hcyclecase with hbot | hwhole
    · exact ((parafermionicCoverFiniteFaceSetBoundaryGraph_ne_bot_iff T).2 hTnonempty) hbot
    · have hlists := parafermionicCoverFiniteFaceChain_toFinset_unique
        T.toList S.toList T.nodup_toList S.nodup_toList (by
          simpa [parafermionicCoverFiniteFaceSetBoundaryGraph] using (hwhole.trans hboundary.symm))
      have hEq : T = S := by
        simpa using hlists
      have hSiT : i ∈ S := by rw [← hEq]; omega
      tauto
  refine ⟨?_⟩
  intro x y
  have hx : C.Reachable root x := by
    cases hxv : x.1 with
    | none =>
      have hEq : x = root := by
        grind [simpleCycleComplementNone]
      rw [hEq]
    | some i =>
      have hiS : i ∉ S := by
        have hxprop := x.2
        simp only [parafermionicCoverSimpleCycleComplementCarrier,
          Set.mem_ofPred_eq] at hxprop
        grind
      have hEq : x = simpleCycleComplementFace S i hiS := by
        apply Subtype.ext
        tauto
      simpa [hEq] using (hroute i hiS)
  have hy : C.Reachable root y := by
    cases hyv : y.1 with
    | none =>
      have hEq : y = root := by
        grind [simpleCycleComplementNone]
      rw [hEq]
    | some i =>
      have hiS : i ∉ S := by
        have hyprop := y.2
        simp only [parafermionicCoverSimpleCycleComplementCarrier,
          Set.mem_ofPred_eq] at hyprop
        grind
      have hEq : y = simpleCycleComplementFace S i hiS := by
        apply Subtype.ext
        tauto
      simpa [hEq] using (hroute i hiS)
  exact hx.symm.trans hy

end PottsDiscontinuity.TorusTopology.Planar.Medial
