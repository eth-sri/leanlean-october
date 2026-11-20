module

public import RequestProject.QCubeFacets

@[expose] public section

/-! The actual oriented edge cycle of a two-dimensional quotient cube. -/
open scoped Classical

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

variable (c : QCube A)

section

variable {v w : V} (hne : v ≠ w) (hs : c.spx = {v, w}) (s : ZMod 2)
include hne hs

theorem squareFacet_v_spx : (qCubeFacet c w s).spx = {v} := by
  simp only [qCubeFacet, hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] <;> grind

theorem squareFacet_w_spx : (qCubeFacet c v s).spx = {w} := by
  simp [qCubeFacet, hs, hne]

end

variable (v w : V) (hne : v ≠ w) (hs : c.spx = {v, w})

/-- The oriented cubical boundary in the direction frame `(v, w)`.
For `w < v`, this agrees with the coordinate incidence convention in `MomentAngle`. -/
noncomputable def cubeSquareEdgeBoundary :=
  oneCubeSubdivision _ v (squareFacet_v_spx c hne hs 0) -
  oneCubeSubdivision _ v (squareFacet_v_spx c hne hs 1) -
  oneCubeSubdivision _ w (squareFacet_w_spx c hne hs 0) +
  oneCubeSubdivision _ w (squareFacet_w_spx c hne hs 1)

/-- Every actual oriented subdivided square boundary is a strict cellular edge cycle. -/
theorem cubeSquareEdgeBoundary_cycle :
    Comb.bdry1 _ (cubeSquareEdgeBoundary c v w hne hs) = 0 := by
  rw [cubeSquareEdgeBoundary, map_add, map_sub, map_sub,
    oneCubeSubdivision_facet_boundary, oneCubeSubdivision_facet_boundary,
    oneCubeSubdivision_facet_boundary, oneCubeSubdivision_facet_boundary]
  rw [qCubeFacet_comm c (Ne.symm hne) 0 0, qCubeFacet_comm c (Ne.symm hne) 0 1,
    qCubeFacet_comm c (Ne.symm hne) 1 0, qCubeFacet_comm c (Ne.symm hne) 1 1]
  abel

end FiniteChains.Davis
