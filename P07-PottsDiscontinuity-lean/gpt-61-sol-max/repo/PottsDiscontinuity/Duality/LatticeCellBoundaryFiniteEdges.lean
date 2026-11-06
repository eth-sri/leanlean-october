/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module
public import Mathlib

public import PottsDiscontinuity.Duality.LatticeCellBoundary
public import Mathlib.Tactic

@[expose] public section

namespace PottsDiscontinuity.FK

open Medial

/-- The graph edge set is exactly the image of the finite set of normalized
boundary bonds under their primal Sym2 representation. -/
theorem latticeCellBoundaryGraph_edgeSet_eq_image (S : Finset LatticeVertex) :
    (latticeCellBoundaryGraph S).edgeSet =
      LatticeBond.toSym2 '' (↑(latticeCellBoundaryBonds S) : Set LatticeBond) := by
  
  ext edge
  obtain ⟨⟨u, v⟩, hEdge⟩ := Sym2.mk_surjective edge
  subst edge
  change s(u, v) ∈ (latticeCellBoundaryGraph S).edgeSet ↔
    s(u, v) ∈ LatticeBond.toSym2 ''  ↑(latticeCellBoundaryBonds S) 
  simp only [SimpleGraph.mem_edgeSet]
  rw [latticeCellBoundaryGraph_adj_iff]
  constructor
  · rintro ⟨hadj, e, heq, hfaces⟩
    exact ⟨e, (mem_latticeCellBoundaryBonds S e).mpr hfaces, heq⟩
  · rintro ⟨e, he, hEq⟩
    
    exact ⟨ by
              have hedge := LatticeBond.toSym2_mem_edgeSet e
              simp_all , e, hEq, (mem_latticeCellBoundaryBonds S e).mp he⟩

theorem latticeCellBoundaryGraph_edgeSet_finite (S : Finset LatticeVertex) :
    ((latticeCellBoundaryGraph S).edgeSet : Set (Sym2 LatticeVertex)).Finite := by
  rw [latticeCellBoundaryGraph_edgeSet_eq_image]
  exact (latticeCellBoundaryBonds_finite S).image LatticeBond.toSym2

end PottsDiscontinuity.FK
