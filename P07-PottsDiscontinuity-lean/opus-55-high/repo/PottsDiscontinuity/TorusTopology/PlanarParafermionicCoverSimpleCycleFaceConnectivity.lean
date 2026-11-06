/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverSimpleCycleFaceIndecomposable
public import PottsDiscontinuity.TorusTopology.PlanarParafermionicCoverFaceAdjacency
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open PottsDiscontinuity.TorusTopology.Planar
open SimpleGraph

theorem parafermionicCoverSimpleCycleFillingSet_induce_faceAdjacency_connected
    {n : ℕ} (hn : 1 ≤ n) {u : ParafermionicCoverBoxVertex n}
    (p : (parafermionicCoverBoxGraph n).Walk u u) (hp : p.IsCycle) :
    ((parafermionicCoverFiniteFaceAdjacencyGraph n).induce
      (↑(parafermionicCoverSimpleCycleFillingSet hn p hp) :
        Set (ParafermionicCoverFiniteFaceTopIndex n))).Connected := by
  classical
  let S := parafermionicCoverSimpleCycleFillingSet hn p hp
  let G := parafermionicCoverFiniteFaceAdjacencyGraph n
  let H := G.induce (↑S : Set (ParafermionicCoverFiniteFaceTopIndex n))
  obtain ⟨_, hSnonempty, _⟩ := (parafermionicCoverSimpleCycleFillingSet_spec hn p hp)
  obtain ⟨a, ha⟩ := hSnonempty
  let anchor : {x : ParafermionicCoverFiniteFaceTopIndex n // x ∈ S} := ⟨a, ha⟩
  let T :=
    S.filter fun j => ∃ hj : j ∈ S, H.Reachable anchor ⟨j, hj⟩
  have hTnonempty : T.Nonempty := by
    refine ⟨a, ?_⟩
    simp only [T, Finset.mem_filter]
    tauto
  have hcross : ∀ i ∈ T, ∀ j ∈ S, j ∉ T →
      Disjoint (parafermionicCoverFiniteFaceBoundaryGraph i.1 i.2).edgeSet
        (parafermionicCoverFiniteFaceBoundaryGraph j.1 j.2).edgeSet := by
    intro i hiT j hjS hjnot
    rw [Set.disjoint_left]
    intro e hei hej
    obtain ⟨hiS, hreach⟩ := ((Finset.mem_filter.mp hiT).2)
    have hne : i ≠ j := by
      intro hij
      subst j
      tauto
    have hadj :=
      (parafermionicCoverFiniteFaceAdjacencyGraph_adj_iff i j).2
        ⟨hne, e, hei, hej⟩
    have hstep : H.Reachable ⟨i, hiS⟩ ⟨j, hjS⟩ := by
      refine ⟨Walk.cons ?_ Walk.nil⟩
      tauto
    exact hjnot (Finset.mem_filter.mpr ⟨hjS, ⟨hjS, (hreach.trans hstep)⟩⟩)
  have hTeq :=
    parafermionicCoverSimpleCycleFillingSet_no_disjoint_nonempty_subfamily
      hn p hp T (Finset.filter_subset _ _) hTnonempty hcross
  rw [connected_iff_exists_forall_reachable]
  refine ⟨anchor, ?_⟩
  rintro ⟨j, hjS⟩
  have hjT : j ∈ T := by rw [hTeq]; omega
  obtain ⟨_, hreach⟩ := (Finset.mem_filter.mp hjT).2
  exact (Reachable.refl anchor).trans hreach

end PottsDiscontinuity.TorusTopology.Planar.Medial
