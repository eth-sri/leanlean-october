import RequestProject.QCubeFacets


/-! The actual oriented edge cycle of a two-dimensional quotient cube. -/
open scoped Classical

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem squareFacet_v_spx (c : QCube A) {v w} (hne : v ≠ w)
    (hs : c.spx = {v, w}) s : (qCubeFacet c w s).spx = {v} := by
  ext x
  simp [qCubeFacet, hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  grind

theorem squareFacet_w_spx (c : QCube A) {v w} (hne : v ≠ w)
    (hs : c.spx = {v, w}) s : (qCubeFacet c v s).spx = {w} := by
  simp [qCubeFacet, hs, hne]

/-- The oriented cubical boundary in the direction frame `(v, w)`.
For `w < v`, this agrees with the coordinate incidence convention in `MomentAngle`. -/
noncomputable def cubeSquareEdgeBoundary (c : QCube A) v w (hne : v ≠ w)
    (hs : c.spx = {v, w}) :=
  oneCubeSubdivision _ v (squareFacet_v_spx c hne hs 0) -
  oneCubeSubdivision _ v (squareFacet_v_spx c hne hs 1) -
  oneCubeSubdivision _ w (squareFacet_w_spx c hne hs 0) +
  oneCubeSubdivision _ w (squareFacet_w_spx c hne hs 1)

/-- Every actual oriented subdivided square boundary is a strict cellular edge cycle. -/
theorem cubeSquareEdgeBoundary_cycle c v w hne
    hs :
    Comb.bdry1 (strictOrderCx (QCube A)) (cubeSquareEdgeBoundary c v w hne hs) = 0 := by
  rw [cubeSquareEdgeBoundary, map_add, map_sub, map_sub,
    oneCubeSubdivision_facet_boundary, oneCubeSubdivision_facet_boundary,
    oneCubeSubdivision_facet_boundary, oneCubeSubdivision_facet_boundary]
  rw [qCubeFacet_comm c hne.symm 0 0, qCubeFacet_comm c hne.symm 0 1,
    qCubeFacet_comm c hne.symm 1 0, qCubeFacet_comm c hne.symm 1 1]
  abel
