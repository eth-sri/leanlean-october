import Mathlib.Tactic

import RequestProject.QCubeThreeFaceIndex
import RequestProject.QCubeOrderedSquareFacets

/-! Geometric edge identifications for the six-face coefficient index. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

  (c : QCube A)
  (u v w : V)
theorem qThreeFaceSquare_zero_small  
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareSmallFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, s, t) := by
  apply Subtype.ext
  rw [qSquareSmallFacet_ordered _ hvw
    (threeFacet_vw_spx c (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne) hs s)]
  rfl

theorem qThreeFaceSquare_zero_large  
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareLargeFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, s, t) := by
  apply Subtype.ext
  rw [qSquareLargeFacet_ordered _ hvw
    (threeFacet_vw_spx c (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne) hs s)]
  rfl

theorem qThreeFaceSquare_one_small  
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareSmallFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, s, t) := by
  apply Subtype.ext
  
  have hspx := threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs s
  have hval : (qThreeFaceSquare c u v w (Ne.symm huv.ne)
      (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs (1, s)).1 =
      qCubeFacet c v s := by
    rfl
  rw [qSquareSmallFacet_ordered _ (hvw.trans huv) (hval.symm ▸ hspx), hval]
  rfl

theorem qThreeFaceSquare_one_large  
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareLargeFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, t, s) := by
  apply Subtype.ext
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hspx := threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs s
  have hval : (qThreeFaceSquare c u v w (Ne.symm huv.ne)
      (Ne.symm (hvw.trans huv).ne) (Ne.symm hvw.ne) hs (1, s)).1 =
      qCubeFacet c v s := by
    rfl
  rw [qSquareLargeFacet_ordered _ (hvw.trans huv) (hval.symm ▸ hspx), hval]
  simpa [qThreeEdge, qThreeEdgeCell, qCubeDoubleFacet, h21] using qCubeFacet_comm c huv.ne s t

theorem qThreeFaceSquare_two_small  
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareSmallFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, t, s) := by
  grind [threeFacet_uv_spx, qThreeFaceSquare, qCubeFacet, qThreeFacetSquare, qCubeFacetIndex, qThreeDirection, qSquareSmallFacet_ordered, qThreeEdge, qThreeEdgeCell, qCubeDoubleFacet, qCubeFacet_comm]

theorem qThreeFaceSquare_two_large  
    (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w}) (s t : ZMod 2) :
    qSquareLargeFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, t, s) := by
  grind [threeFacet_uv_spx, qThreeFaceSquare, qCubeFacet, qThreeFacetSquare, qCubeFacetIndex, qThreeDirection, qSquareLargeFacet_ordered, qThreeEdge, qThreeEdgeCell, qCubeDoubleFacet, qCubeFacet_comm]

end FiniteChains.Davis
