/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Adaptation: Namespace and import relocation only. -/
module
public import Mathlib

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.TorusTopology.Planar.Medial



/-- An even-degree subgraph of the spanning graph of a finite simple cycle is
empty or the whole cycle. -/
theorem evenSubgraphOfCycle_eq_bot_or_cycle
    {V : Type*} [Finite V] {G : SimpleGraph V} {u : V}
    (p : G.Walk u u) (hp : p.IsCycle) (H : SimpleGraph V)
    (hsub : H ≤ p.toSubgraph.spanningCoe)
    (heven : ∀ v : V, Even (H.neighborSet v).ncard) :
    H = ⊥ ∨ H = p.toSubgraph.spanningCoe := by
  
  let C := p.toSubgraph.spanningCoe
  
  have hfull_of_neighbor (v : V) (hv : v ∈ p.support)
      (hnon : (H.neighborSet v).Nonempty) :
      H.neighborSet v = C.neighborSet v := by
    have hsubN  := SimpleGraph.neighborSet_mono hsub v
    have hCcard : (C.neighborSet v).ncard = 2 := hp.ncard_neighborSet_toSubgraph_eq_two hv
    have hle  := Trans.trans (Set.ncard_le_ncard hsubN (Set.toFinite (C.neighborSet v))) hCcard
    have hpos  := (Set.ncard_pos (Set.toFinite _)).mpr hnon
    
    apply Set.eq_of_subset_of_ncard_le hsubN
    rw [hCcard, (by
                   grind : (H.neighborSet v).ncard = 2)]
  by_cases hbot : H = ⊥
  · exact Or.inl hbot
  · obtain ⟨a, b, hab⟩ := (SimpleGraph.ne_bot_iff_exists_adj).mp hbot
    
    have haV  := p.toSubgraph.edge_vert (hsub hab)
    
    
    have hprop : ∀ {x y }
        (w : p.toSubgraph.coe.Walk x y),
        H.neighborSet x.1 = C.neighborSet x.1 →
          H.neighborSet y.1 = C.neighborSet y.1 := by
      intro x y w
      induction w with
      | nil => intro hx; exact hx
      | @cons x y z hadj tail ih =>
          intro hx
          have hadjC  := hadj
          have hyC  := (C.mem_neighborSet x.1 y.1).mpr hadjC
          have hyH : y.1 ∈ H.neighborSet x.1 := by simpa [hx] using hyC
          have hadjH  := (H.mem_neighborSet x.1 y.1).mp hyH
          have hxH  :=
            (H.mem_neighborSet y.1 x.1).mpr  hadjH.symm 
          have hySupport  :=
            p.mem_verts_toSubgraph.mp y.2
          have hnext  :=
            hfull_of_neighbor y.1 hySupport ⟨x.1, hxH⟩
          exact ih hnext
    have hfull : ∀ v , v ∈ p.support →
        H.neighborSet v = C.neighborSet v := by
      intro v hv
      
      
       
      rcases (p.toSubgraph_connected  ⟨a, haV⟩   ⟨v, p.mem_verts_toSubgraph.mpr hv⟩) with ⟨w⟩
      exact hprop w (hfull_of_neighbor a (p.mem_verts_toSubgraph.mp haV) ⟨b, (H.mem_neighborSet a b).mpr hab⟩)
    apply Or.inr
    apply le_antisymm hsub
    intro x y hxy
    
    
    
    
    
    exact (H.mem_neighborSet x y).mp (by simpa [(hfull x (p.mem_verts_toSubgraph.mp (p.toSubgraph.edge_vert hxy)))] using  (C.mem_neighborSet x y).mpr hxy )

end PottsDiscontinuity.TorusTopology.Planar.Medial
