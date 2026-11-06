/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCyclePivotAcyclic
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCyclePivotCarrier
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial




section

variable {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n} (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle)


/-- The actual pivot-deleted graph of a named actual simple-cycle filling is a
 tree when induced on the original carrier of its actual face union. -/
theorem parafermionicCoverSimpleCycleFilling_inducedGraph_isTree
     :
    ((parafermionicCoverFiniteFaceSetWithoutPivotsGraph
        (parafermionicCoverSimpleCycleFillingSet hn p hp)).induce
      (parafermionicCoverFiniteFaceUnionCarrier
        (parafermionicCoverSimpleCycleFillingSet hn p hp))).IsTree := by
                                                                        solve_by_elim [_root_.SimpleGraph.IsTree.mk, _root_.SimpleGraph.IsAcyclic.induce, _root_.PottsDiscontinuity.TorusTopology.Planar.Medial.parafermionicCoverSimpleCyclePivotAcyclic, _root_.PottsDiscontinuity.TorusTopology.Planar.Medial.parafermionicCoverSimpleCyclePivotGraph_induce_carrier_connected]

/-- Euler's vertex-edge count for the actual tree obtained from a named
simple-cycle filling and its actual retained-face union carrier. -/
theorem parafermionicCoverSimpleCycleFilling_euler_count
     :
    Nat.card (parafermionicCoverFiniteFaceUnionCarrier
      (parafermionicCoverSimpleCycleFillingSet hn p hp)) +
      (parafermionicCoverSimpleCycleFillingSet hn p hp).card =
      (parafermionicCoverFiniteFaceSetEdgeSupport
        (parafermionicCoverSimpleCycleFillingSet hn p hp)).card + 1 := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let R := parafermionicCoverFiniteFaceSetWithoutPivotsGraph S
  let C := parafermionicCoverFiniteFaceUnionCarrier S
  let H := R.induce C
  
  
  have hnat : Nat.card {e // e ∈ H.edgeSet} + 1 = Nat.card C := by
    calc
      Nat.card {e // e ∈ H.edgeSet} + 1 =
          Fintype.card {e // e ∈ H.edgeSet} + 1 := by
            rw [Nat.card_eq_fintype_card]
      _ = Finset.card H.edgeFinset + 1 := by
        rw [← SimpleGraph.edgeFinset_card]
      _ = Fintype.card C := by simpa [H] using ((parafermionicCoverSimpleCycleFilling_inducedGraph_isTree hn p hp).card_edgeFinset)
      _ = Nat.card C := by rw [Nat.card_eq_fintype_card]
  
  have hcount' : Nat.card {e // e ∈ H.edgeSet} + S.card =
      (parafermionicCoverFiniteFaceSetEdgeSupport S).card := by
    simpa [H, R, C] using  parafermionicCoverFiniteFaceSetWithoutPivotsGraph_induce_carrier_edge_card_add_faces S 
  grind

end

end PottsDiscontinuity.TorusTopology.Planar.Medial
