module
public import Mathlib

public import PottsDiscontinuity.RCInfinite.OpeningPaths

@[expose] public section

open Set

namespace PottsDiscontinuity.RCInfinite
open FK
noncomputable section
open scoped Classical

/-- If new edges have both endpoints in a finite set, every new infinite
component contains an old infinite component. -/
theorem infinite_component_contains_old
    {V : Type*} {G H : SimpleGraph V} (hGH : G ≤ H) (S : Finset V)
    (hnew : ∀ x y, H.Adj x y → ¬G.Adj x y → x ∈ S ∧ y ∈ S)
    (x : V) (hinf : {y | H.Reachable x y}.Infinite) :
    ∃ z, H.Reachable x z ∧ {y | G.Reachable z y}.Infinite := by
  have hwalk {u v : V} (w : H.Walk u v) :
      ∃ z, (z = u ∨ z ∈ S) ∧ G.Reachable z v := by
    induction w with
    | nil => simp_all
    | @cons u v t huv w ih =>
      obtain ⟨z, hz, hzt⟩ := ih
      rcases hz with hz | hz
      · subst z
        by_cases hold : G.Adj u v
        · exact ⟨u, Or.inl rfl, hold.reachable.trans hzt⟩
        · grind
      · exact ⟨z, Or.inr hz, hzt⟩
  let T  := (insert x S).filter (H.Reachable x)
  
  by_contra! hnone
  have hfinite : (⋃ z ∈  T , {y | G.Reachable z y}).Finite := by
    apply T.finite_toSet.biUnion
    grind
  exact hinf (hfinite.subset (by
                                intro y hxy
                                obtain ⟨w⟩ := hxy
                                obtain ⟨z, hz, hzy⟩ := hwalk w
                                
                                refine mem_iUnion.mpr ⟨z, mem_iUnion.mpr ⟨?_, hzy⟩⟩
                                exact Finset.mem_filter.mpr ⟨Finset.mem_insert.mpr hz,  w.reachable.trans (hzy.mono hGH).symm ⟩))

def edgeEndpoints (F : Finset Edge) : Finset LatticeVertex :=
  F.biUnion fun e => e.val.toFinset

theorem opening_new_edge_endpoints (F : Finset Edge) (ω : LatticeConfiguration)
    (x y : LatticeVertex)
    (hnew : (rcInfiniteOpenGraph (setEdges F (fun _ => true) ω)).Adj x y)
    (hold : ¬(rcInfiniteOpenGraph ω).Adj x y) :
    x ∈ edgeEndpoints F ∧ y ∈ edgeEndpoints F := by
  obtain ⟨he, hω⟩ := (rcInfiniteOpenGraph_adj _ x y).mp hnew
  have hF :  ⟨s(x, y), he⟩  ∈ F := by
    by_contra hF
    apply hold
    apply (rcInfiniteOpenGraph_adj _ x y).mpr
    exact ⟨he, by simpa only [setEdges, hF, ite_false] using hω⟩
  constructor
  · exact Finset.mem_biUnion.mpr ⟨⟨s(x, y), he⟩, hF, by simp ⟩
  · exact Finset.mem_biUnion.mpr ⟨⟨s(x, y), he⟩, hF, by simp ⟩

theorem opening_infinite_component_contains_old (F : Finset Edge)
    (ω : LatticeConfiguration) (x : LatticeVertex)
    (hx : setEdges F (fun _ => true) ω ∈ infiniteAt x) :
    ∃ z, (rcInfiniteOpenGraph (setEdges F (fun _ => true) ω)).Reachable x z ∧
      ω ∈ infiniteAt z :=
  by
    solve_by_elim [_root_.PottsDiscontinuity.RCInfinite.infinite_component_contains_old, _root_.PottsDiscontinuity.RCInfinite.opening_graph_mono, _root_.PottsDiscontinuity.RCInfinite.opening_new_edge_endpoints]

end
end PottsDiscontinuity.RCInfinite
