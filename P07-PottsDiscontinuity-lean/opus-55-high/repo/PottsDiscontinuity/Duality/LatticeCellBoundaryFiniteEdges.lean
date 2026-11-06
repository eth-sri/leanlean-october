/- Adapted from an earlier, unpublished formalization of the planar FK model by the same author.
Namespaces/imports adapted to the shared FK library. -/
module

public import PottsDiscontinuity.Duality.LatticeCellBoundary
public import Mathlib.Tactic

public section

namespace PottsDiscontinuity.FK

open Medial

section
variable (S : Finset LatticeVertex)
/-- The graph edge set is exactly the image of the finite set of normalized
boundary bonds under their primal Sym2 representation. -/
theorem latticeCellBoundaryGraph_edgeSet_eq_image  :
    (latticeCellBoundaryGraph S).edgeSet =
      LatticeBond.toSym2 '' (↑(latticeCellBoundaryBonds S) : Set LatticeBond) := by
  ext edge
  obtain ⟨⟨u, v⟩, hEdge⟩ := Sym2.mk_surjective edge
  subst edge
  simp
  rw [latticeCellBoundaryGraph_adj_iff]
  constructor
  · rintro ⟨hadj, e, heq, hfaces⟩
    exact ⟨e, (mem_latticeCellBoundaryBonds S e).mpr hfaces, heq⟩
  · rintro ⟨e, he, hEq⟩
    have hsq : squareLattice.Adj u v := by
      have hedge := LatticeBond.toSym2_mem_edgeSet e
      simp_all
    exact ⟨hsq, e, hEq, (mem_latticeCellBoundaryBonds S e).mp he⟩

theorem latticeCellBoundaryGraph_edgeSet_finite  :
    ((latticeCellBoundaryGraph S).edgeSet : Set (Sym2 LatticeVertex)).Finite := by
  rw [latticeCellBoundaryGraph_edgeSet_eq_image]
  exact (latticeCellBoundaryBonds_finite S).image LatticeBond.toSym2
end

end PottsDiscontinuity.FK
