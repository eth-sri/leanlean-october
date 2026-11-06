/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.FiniteEvenEdgeCycle
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.FK

open SimpleGraph

/-- In a graph with finite edge set and even degree at every vertex, every edge
lies on an actual simple cycle, even when the vertex type is infinite. -/
theorem edge_mem_some_isCycle_of_even_degree_of_finite_edgeSet
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfinite : G.edgeSet.Finite)
    (heven : ∀ x : V, Even (G.neighborSet x).ncard)
    {u w : V} (huw : G.Adj u w) :
    ∃ (z : V) (p : G.Walk z z), p.IsCycle ∧ s(u,w) ∈ p.edges := by
  
  let U  := {x | ∃ e ∈ G.edgeSet, x ∈ e.toFinset}
  
  let : Finite ↑U :=  by
                        rw [show U = ⋃ e ∈ G.edgeSet,  e.toFinset  by
                          ext x
                          simp [U]]
                        exact hfinite.biUnion fun e he => Finset.finite_toSet _ 
  let : Fintype U := Fintype.ofFinite U
  let H  := G.induce U
  have hu : u ∈ U := by
    refine ⟨s(u,w), G.mem_edgeSet.mpr huw, ?_⟩
    simp
  have hw : w ∈ U := by
    refine ⟨s(u,w), G.mem_edgeSet.mpr huw, ?_⟩
    simp
  have hneighbors (x : V) (hx : x ∈ U) : G.neighborSet x ⊆ U := by
    intro y hy
    refine ⟨s(x,y), G.mem_edgeSet.mpr ((G.mem_neighborSet x y).mp hy), ?_⟩
    simp
  
  have hAdj : H.Adj ⟨u,hu⟩ ⟨w,hw⟩ := huw
  obtain ⟨z,q,hq,he⟩ := edge_mem_some_isCycle_of_even_degree H (by
                                                                  intro x
                                                                  have hnc : (H.neighborSet x).ncard = (G.neighborSet x.1).ncard := Set.ncard_congr (fun y hy => ↑y) (fun y hy => (mem_neighborSet G ↑x ↑y).mpr ((mem_neighborSet H x y).mp hy))
                                                                                                                                      (fun y z hy hz => Subtype.ext) fun y hy =>
                                                                                                                                      have hyU := hneighbors  ↑x  x.property hy;
                                                                                                                                      Exists.intro ⟨y, hyU⟩ (Exists.intro ((mem_neighborSet G  ↑x  y).mpr hy) rfl)
                                                                  rw [← H.ncard_neighborSet, hnc]
                                                                  exact heven x.1) hAdj
  let f : H →g G := { toFun := Subtype.val, map_rel' := by intro a b h; exact h }
  let p := q.map f
  
  
  exact ⟨f z, p,  (q.isCycle_map_iff_of_injective Subtype.val_injective).mpr hq ,  by
                        have hmap : p.edges = q.edges.map (Sym2.map f) := Walk.edges_map f q
                        rw [hmap]
                        exact List.mem_map.mpr ⟨s(⟨u,hu⟩,⟨w,hw⟩), he, rfl⟩ ⟩

end PottsDiscontinuity.FK
