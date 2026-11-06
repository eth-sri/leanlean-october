import Mathlib.Tactic

import RequestProject.QCubeFacets

/-! The actual oriented edge cycle of a two-dimensional quotient cube. -/


namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

  (c : QCube A)
theorem squareFacet_v_spx  {v w : V} (hne : v ≠ w)
    (hs : c.spx = {v, w}) (s : ZMod 2) : (qCubeFacet c w s).spx = {v} := by aesop (add simp [qCubeFacet])

theorem squareFacet_w_spx  {v w : V} (hne : v ≠ w)
    (hs : c.spx = {v, w}) (s : ZMod 2) : (qCubeFacet c v s).spx = {w} := by
  simp [qCubeFacet, hs, hne]

/-- The oriented cubical boundary in the direction frame `(v, w)`.
For `w < v`, this agrees with the coordinate incidence convention in `MomentAngle`. -/
noncomputable def cubeSquareEdgeBoundary  (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w})  :=
  oneCubeSubdivision (qCubeFacet c w 0) v (squareFacet_v_spx c hne hs 0) -
  oneCubeSubdivision (qCubeFacet c w 1) v (squareFacet_v_spx c hne hs 1) -
  oneCubeSubdivision (qCubeFacet c v 0) w (squareFacet_w_spx c hne hs 0) +
  oneCubeSubdivision (qCubeFacet c v 1) w (squareFacet_w_spx c hne hs 1)

/-- Every actual oriented subdivided square boundary is a strict cellular edge cycle. -/
theorem cubeSquareEdgeBoundary_cycle  (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) :
    Comb.bdry1 (strictOrderCx (QCube A)) (cubeSquareEdgeBoundary c v w hne hs) = 0 := by
  rw [cubeSquareEdgeBoundary, map_add, map_sub, map_sub,
    oneCubeSubdivision_facet_boundary, oneCubeSubdivision_facet_boundary,
    oneCubeSubdivision_facet_boundary, oneCubeSubdivision_facet_boundary]
  rw [qCubeFacet_comm c (Ne.symm hne) 0 0, qCubeFacet_comm c (Ne.symm hne) 0 1,
    qCubeFacet_comm c (Ne.symm hne) 1 0, qCubeFacet_comm c (Ne.symm hne) 1 1]
  abel

end FiniteChains.Davis
