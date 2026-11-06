/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial

open SimpleGraph

/-- An even-degree subgraph of the spanning graph of a finite simple cycle is
empty or the whole cycle. -/
theorem evenSubgraphOfCycle_eq_bot_or_cycle
    {V : Type*} [Finite V] {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hp : p.IsCycle) (H : SimpleGraph V)
    (hsub : H ≤ p.toSubgraph.spanningCoe)
    (heven : ∀ v : V, Even (H.neighborSet v).ncard) :
    H = ⊥ ∨ H = p.toSubgraph.spanningCoe := by
  let C := p.toSubgraph.spanningCoe
  have hneighborC (v : V) : C.neighborSet v = p.toSubgraph.neighborSet v := by
    rfl
  have hfull_of_neighbor (v : V) (hv : v ∈ p.support)
      (hnon : (H.neighborSet v).Nonempty) :
      H.neighborSet v = C.neighborSet v := by
    have hsubN : H.neighborSet v ⊆ C.neighborSet v := by tauto
    have hCcard : (C.neighborSet v).ncard = 2 :=
      hp.ncard_neighborSet_toSubgraph_eq_two hv
    have hle : (H.neighborSet v).ncard ≤ 2 := by
      calc
        (H.neighborSet v).ncard ≤ (C.neighborSet v).ncard := Set.ncard_le_ncard hsubN
        _ = 2 := hCcard
    have hpos := (Set.ncard_pos (Set.toFinite _)).mpr hnon
    have hHcard : (H.neighborSet v).ncard = 2 := by
      grind
    apply Set.eq_of_subset_of_ncard_le hsubN
    omega
  by_cases hbot : H = ⊥
  · simp_all
  · obtain ⟨a, b, hab⟩ := (SimpleGraph.ne_bot_iff_exists_adj).mp hbot
    have haV := p.toSubgraph.edge_vert (hsub hab)
    have haSupport := p.mem_verts_toSubgraph.mp haV
    have hprop : ∀ {x y : p.toSubgraph.verts}
        (w : p.toSubgraph.coe.Walk x y),
        H.neighborSet x.1 = C.neighborSet x.1 →
          H.neighborSet y.1 = C.neighborSet y.1 := by
      intro x y w
      induction w with
      | nil => simp
      | @cons x y z hadj tail ih =>
          intro hx
          have hyH : y.1 ∈ H.neighborSet x.1 := by simp_all
          have hadjH : H.Adj x.1 y.1 := by tauto
          have hnext :=
            hfull_of_neighbor y.1 (p.mem_verts_toSubgraph.mp y.2) ⟨x.1, (by tauto)⟩
          simp_all
    have hfull : ∀ v : V, v ∈ p.support →
        H.neighborSet v = C.neighborSet v := by
      intro v hv
      let av : p.toSubgraph.verts := ⟨a, haV⟩
      let vv : p.toSubgraph.verts := ⟨v, p.mem_verts_toSubgraph.mpr hv⟩
      rcases (p.toSubgraph_connected av vv) with ⟨w⟩
      exact hprop w (by tauto)
    apply Or.inr
    apply le_antisymm hsub
    intro x y hxy
    have hxSupport := p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hxy)
    have hyC : y ∈ C.neighborSet x := by tauto
    have hyH : y ∈ H.neighborSet x := by grind
    tauto

end PottsDiscontinuity.TorusTopology.Planar.Medial
