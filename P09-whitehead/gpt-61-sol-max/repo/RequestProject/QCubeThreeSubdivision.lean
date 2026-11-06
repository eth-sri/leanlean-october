import Mathlib.Tactic

import RequestProject.QCubeSquareSubdivision
import RequestProject.StrictLowerIntervalChains

/-! Actual strict subdivisions of quotient three-cubes. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

  (c : QCube A)
  {u v w : V}
theorem threeFacet_uv_spx  
    (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c w s).spx = {u, v} := by
  aesop (add simp [qCubeFacet])

theorem threeFacet_uw_spx  
    (huv : u ≠ v) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c v s).spx = {u, w} := by
  grind [threeFacet_uv_spx]

theorem threeFacet_vw_spx  
    (huv : u ≠ v) (huw : u ≠ w) (hs : c.spx = {u, v, w}) (s : ZMod 2) :
    (qCubeFacet c u s).spx = {v, w} := by
  grind [threeFacet_uv_spx]

noncomputable def cubeThreeSquareBoundary  (u v w : V)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w})  :=
  cubeSquareSubdivision (qCubeFacet c w 0) u v huv (threeFacet_uv_spx c huw hvw hs 0) -
  cubeSquareSubdivision (qCubeFacet c w 1) u v huv (threeFacet_uv_spx c huw hvw hs 1) -
  cubeSquareSubdivision (qCubeFacet c v 0) u w huw (threeFacet_uw_spx c huv hvw hs 0) +
  cubeSquareSubdivision (qCubeFacet c v 1) u w huw (threeFacet_uw_spx c huv hvw hs 1) +
  cubeSquareSubdivision (qCubeFacet c u 0) v w hvw (threeFacet_vw_spx c huv huw hs 0) -
  cubeSquareSubdivision (qCubeFacet c u 1) v w hvw (threeFacet_vw_spx c huv huw hs 1)

end FiniteChains.Davis
