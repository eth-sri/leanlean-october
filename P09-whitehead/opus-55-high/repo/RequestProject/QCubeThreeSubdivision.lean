import RequestProject.QCubeSquareSubdivision
import RequestProject.StrictLowerIntervalChains


/-! Actual strict subdivisions of quotient three-cubes. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

theorem threeFacet_uv_spx (c : QCube A) {u v w}
    (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) s :
    (qCubeFacet c w s).spx = {u, v} := by
  ext x
  simp [qCubeFacet, hs, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
  grind

theorem threeFacet_uw_spx (c : QCube A) {u v w}
    (huv : u ≠ v) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) s :
    (qCubeFacet c v s).spx = {u, w} := by
  apply threeFacet_uv_spx c huv hvw.symm
  grind

theorem threeFacet_vw_spx (c : QCube A) {u v w}
    (huv : u ≠ v) (huw : u ≠ w) (hs : c.spx = {u, v, w}) s :
    (qCubeFacet c u s).spx = {v, w} := by
  apply threeFacet_uv_spx c huv.symm huw.symm
  grind

noncomputable def cubeThreeSquareBoundary (c : QCube A) u v w
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) (hs : c.spx = {u, v, w}) :=
  cubeSquareSubdivision _ u v huv (threeFacet_uv_spx c huw hvw hs 0) -
  cubeSquareSubdivision _ u v huv (threeFacet_uv_spx c huw hvw hs 1) -
  cubeSquareSubdivision _ u w huw (threeFacet_uw_spx c huv hvw hs 0) +
  cubeSquareSubdivision _ u w huw (threeFacet_uw_spx c huv hvw hs 1) +
  cubeSquareSubdivision _ v w hvw (threeFacet_vw_spx c huv huw hs 0) -
  cubeSquareSubdivision _ v w hvw (threeFacet_vw_spx c huv huw hs 1)
