module

public import RequestProject.QCubeThreeFaceIndex
public import RequestProject.QCubeOrderedSquareFacets

@[expose] public section

/-! Geometric edge identifications for the six-face coefficient index. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

variable (c : QCube A) (u v w : V)
  (huv : v < u) (hvw : w < v) (hs : c.spx = {u, v, w})

local notation "face" => qThreeFaceSquare c u v w
  (ne_of_gt huv) (ne_of_gt (lt_trans hvw huv)) (ne_of_gt hvw) hs
local notation "edge" => qThreeEdge c u v w
  (ne_of_gt huv) (ne_of_gt (lt_trans hvw huv)) (ne_of_gt hvw) hs

/-- Smaller oriented facets of the three square directions. -/
theorem qThreeFaceSquare_small (k : Fin 3) (s t : ZMod 2) :
    qSquareSmallFacet (face (k, s)) t = edge (![ (1, s, t), (2, s, t), (2, t, s) ] k) := by
  fin_cases k <;> apply Subtype.ext
  · rw [qSquareSmallFacet_ordered _ hvw
      (threeFacet_vw_spx c huv.ne' (hvw.trans huv).ne' hs s)]
    rfl
  · rw [qSquareSmallFacet_ordered _ (hvw.trans huv)
      (threeFacet_uw_spx c huv.ne' hvw.ne' hs s)]
    rfl
  · rw [qSquareSmallFacet_ordered _ huv
      (threeFacet_uv_spx c (hvw.trans huv).ne' hvw.ne' hs s)]
    exact qCubeFacet_comm c hvw.ne s t

/-- Larger oriented facets; the index records the order of the two facet signs. -/
theorem qThreeFaceSquare_large (k : Fin 3) (s t : ZMod 2) :
    qSquareLargeFacet (face (k, s)) t = edge (![ (0, s, t), (0, t, s), (1, t, s) ] k) := by
  fin_cases k <;> apply Subtype.ext
  · rw [qSquareLargeFacet_ordered _ hvw
      (threeFacet_vw_spx c huv.ne' (hvw.trans huv).ne' hs s)]
    rfl
  · rw [qSquareLargeFacet_ordered _ (hvw.trans huv)
      (threeFacet_uw_spx c huv.ne' hvw.ne' hs s)]
    exact qCubeFacet_comm c huv.ne s t
  · rw [qSquareLargeFacet_ordered _ huv
      (threeFacet_uv_spx c (hvw.trans huv).ne' hvw.ne' hs s)]
    exact qCubeFacet_comm c (hvw.trans huv).ne s t

end FiniteChains.Davis
