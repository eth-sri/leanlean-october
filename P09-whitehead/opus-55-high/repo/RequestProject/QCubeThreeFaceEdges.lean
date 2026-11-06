import RequestProject.QCubeThreeFaceIndex
import RequestProject.QCubeOrderedSquareFacets


/-! Geometric edge identifications for the six-face coefficient index. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

theorem qThreeFaceSquare_zero_small (c : QCube A) u v w
    huv (hvw : w < v) hs s t :
    qSquareSmallFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, s, t) := by
  apply Subtype.ext
  rw [qSquareSmallFacet_ordered _ hvw
    (threeFacet_vw_spx c (Ne.symm huv.ne) (by grind) hs s)]
  rfl

theorem qThreeFaceSquare_zero_large (c : QCube A) u v w
    huv (hvw : w < v) hs s t :
    qSquareLargeFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, s, t) := by
  apply Subtype.ext
  rw [qSquareLargeFacet_ordered _ hvw
    (threeFacet_vw_spx c (Ne.symm huv.ne) (by grind) hs s)]
  rfl

theorem qThreeFaceSquare_one_small (c : QCube A) u v w
    huv (hvw : w < v) hs s t :
    qSquareSmallFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, s, t) := by
  apply Subtype.ext
  have hspx := threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs s
  have hval : (qThreeFaceSquare c u v w (Ne.symm huv.ne)
      (by grind) (Ne.symm hvw.ne) hs (1, s)).1 =
      qCubeFacet c v s := by
    rfl
  rw [qSquareSmallFacet_ordered _ (hvw.trans huv) (hval.symm ▸ hspx), hval]
  rfl

theorem qThreeFaceSquare_one_large (c : QCube A) u v w
    huv (hvw : w < v) hs s t :
    qSquareLargeFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (0, t, s) := by
  apply Subtype.ext
  have h21 : (2) ≠ 1 := by decide
  have hspx := threeFacet_uw_spx c (Ne.symm huv.ne) (Ne.symm hvw.ne) hs s
  have hval : (qThreeFaceSquare c u v w (Ne.symm huv.ne)
      (by grind) (Ne.symm hvw.ne) hs (1, s)).1 =
      qCubeFacet c v s := by
    rfl
  rw [qSquareLargeFacet_ordered _ (hvw.trans huv) (hval.symm ▸ hspx), hval]
  simpa [qThreeEdge, qThreeEdgeCell, qCubeDoubleFacet, h21] using qCubeFacet_comm c huv.ne s t

theorem qThreeFaceSquare_two_small (c : QCube A) u v w
    huv (hvw : w < v) hs s t :
    qSquareSmallFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, t, s) := by
  apply Subtype.ext
  have h21 : (2) ≠ 1 := by decide
  have hspx := threeFacet_uv_spx c (by grind) (Ne.symm hvw.ne) hs s
  have hval : (qThreeFaceSquare c u v w (Ne.symm huv.ne)
      (by grind) (Ne.symm hvw.ne) hs (2, s)).1 =
      qCubeFacet c w s := by
    rfl
  rw [qSquareSmallFacet_ordered _ huv (hval.symm ▸ hspx), hval]
  simpa [qThreeEdge, qThreeEdgeCell, qCubeDoubleFacet, h21] using qCubeFacet_comm c hvw.ne s t

theorem qThreeFaceSquare_two_large (c : QCube A) u v w
    huv (hvw : w < v) hs s t :
    qSquareLargeFacet
      (qThreeFaceSquare c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (2, s)) t =
      qThreeEdge c u v w (Ne.symm huv.ne) (Ne.symm (hvw.trans huv).ne)
        (Ne.symm hvw.ne) hs (1, t, s) := by
  apply Subtype.ext
  have h21 : (2) ≠ 1 := by decide
  have hspx := threeFacet_uv_spx c (by grind) (Ne.symm hvw.ne) hs s
  have hval : (qThreeFaceSquare c u v w (Ne.symm huv.ne)
      (by grind) (Ne.symm hvw.ne) hs (2, s)).1 =
      qCubeFacet c w s := by
    rfl
  rw [qSquareLargeFacet_ordered _ huv (hval.symm ▸ hspx), hval]
  simpa [qThreeEdge, qThreeEdgeCell, qCubeDoubleFacet, h21] using qCubeFacet_comm c (hvw.trans huv).ne s t
