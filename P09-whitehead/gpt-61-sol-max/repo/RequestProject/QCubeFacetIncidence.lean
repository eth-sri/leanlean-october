import Mathlib.Tactic

import RequestProject.QCubeThreeSubdivision
import RequestProject.MomentAngle

/-! Actual quotient facets have the cubical collapse's coordinate incidence signs. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [Fintype V] [LinearOrder V] {A : CommRel V}

  (c : QCube A)
theorem qCubeFacet_incidence_zero  (v : V) :
    incid (qCubeToCoordinate (qCubeFacet c v 0)) v =
      (-1 : ℤ) ^ ((c.spx.erase v).filter (fun i => i < v)).card := by
  simp [incid, qCubeToCoordinate, qCubeFacet, CubeCoord.sgn]

theorem qCubeFacet_incidence_one  (v : V) :
    incid (qCubeToCoordinate (qCubeFacet c v 1)) v =
      -((-1 : ℤ) ^ ((c.spx.erase v).filter (fun i => i < v)).card) := by
  simp_all [incid, qCubeToCoordinate, qCubeFacet, CubeCoord.sgn]

/-- The six signs of an actual three-cube in decreasing coordinate order. -/
theorem threeFacet_incidence_zero  {u v w : V}
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) :
    incid (qCubeToCoordinate (qCubeFacet c w 0)) w = 1 ∧
    incid (qCubeToCoordinate (qCubeFacet c v 0)) v = -1 ∧
    incid (qCubeToCoordinate (qCubeFacet c u 0)) u = 1 := by
  have huw := hvw.trans huv
  have he : ({v, w} : Finset V).erase u = {v, w} :=
    Finset.erase_eq_of_notMem (by simp [Ne.symm huv.ne, Ne.symm huw.ne])
  simp [qCubeFacet_incidence_zero, hs, Finset.filter_erase, Finset.filter_insert, Finset.filter_singleton,
    huv, hvw, huw, not_lt_of_ge huv.le, not_lt_of_ge hvw.le, not_lt_of_ge huw.le,
    he, Ne.symm hvw.ne]

theorem threeFacet_incidence_one  {u v w : V}
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) :
    incid (qCubeToCoordinate (qCubeFacet c w 1)) w = -1 ∧
    incid (qCubeToCoordinate (qCubeFacet c v 1)) v = 1 ∧
    incid (qCubeToCoordinate (qCubeFacet c u 1)) u = -1 := by
  obtain ⟨hw, hv, hu⟩ := threeFacet_incidence_zero c huv hvw hs
  simp only [qCubeFacet_incidence_zero] at hw hv hu
  simp only [qCubeFacet_incidence_one, hw, hv, hu]
  norm_num

end FiniteChains.Davis
