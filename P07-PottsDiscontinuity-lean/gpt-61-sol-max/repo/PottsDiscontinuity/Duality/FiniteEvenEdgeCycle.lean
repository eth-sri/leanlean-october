/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.FiniteGraphBoundaryParity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.FK



/-- Every edge of a finite even-degree graph lies on a genuine simple cycle. -/
theorem edge_mem_some_isCycle_of_even_degree
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (heven : ∀ x : V, Even (G.degree x)) {u w : V} (huw : G.Adj u w) :
    ∃ (z : V) (p : G.Walk z z), p.IsCycle ∧ s(u,w) ∈ p.edges := by
  
  have hne  := G.ne_of_adj huw
  let H := G.deleteEdges {s(u,w)}
  have hNFu : H.neighborFinset u = G.neighborFinset u \ {w} := by
    aesop
  
  have hNFother (x : V) (hxU : x ≠ u) (hxW : x ≠ w) :
      H.neighborFinset x = G.neighborFinset x := by
    
    aesop
  have hdegU : H.degree u = G.degree u - 1 := by
    calc
      H.degree u = (H.neighborFinset u).card := by rw [SimpleGraph.card_neighborFinset_eq_degree]
      _ = (G.neighborFinset u \ {w}).card := by rw [hNFu]
      _ = (G.neighborFinset u).card - 1 := by
        rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem
          ((G.mem_neighborFinset u w).mpr huw)]
      _ = G.degree u - 1 := by rw [SimpleGraph.card_neighborFinset_eq_degree]
  
  
  
  
  have hreach := exists_reachable_between_of_odd_degree_sum H {u} {w}
    (by
       simp_all) (by
             intro x hx
             have hx' : x ≠ u ∧ x ≠ w := by simpa using hx
             have hxU := hx'.1
             have hxW := hx'.2
             rw [← SimpleGraph.card_neighborFinset_eq_degree, hNFother x hxU hxW]
             exact heven x) (by
                        simp only [Finset.sum_singleton]
                        
                        obtain ⟨k,hk⟩ := heven u
                        have hv  := (G.mem_neighborFinset u w).mpr huw
                        have hkpos : 0 < k := by
                          have hpos : 0 < G.degree u := by
                            rw [← SimpleGraph.card_neighborFinset_eq_degree]
                            grind
                          omega
                        refine ⟨k-1, ?_⟩
                        omega)
  obtain ⟨x,hx,y,hy,hxy⟩ := hreach
  have hxu : x = u := by simpa using hx
  have hyw : y = w := by simpa using hy
  subst x
  subst y
  have hxy'  := hxy
  exact (SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle).mp ⟨huw,hxy'⟩

end PottsDiscontinuity.FK
