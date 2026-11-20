module

public import RequestProject.QCubeThreeFaceIndex
public import RequestProject.QCubeOrderedSquareFacets
public import RequestProject.CubicalThreeBoundaryMatrix

@[expose] public section

/-! Both boundary directions for a facet in the canonical decreasing frame. -/
noncomputable section
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] [LinearOrder V] {A : CommRel V}

variable (c : QThreeCube A)

theorem qThreeFaceEdges (i : Fin 3 × ZMod 2) (t : ZMod 2) :
    qSquareSmallFacet (qThreeFaceSquare c i) t = qThreeEdge c (smallEdgeIndex i t) ∧
    qSquareLargeFacet (qThreeFaceSquare c i) t = qThreeEdge c (largeEdgeIndex i t) := by
  obtain ⟨e, s⟩ := i
  have h0 := threeFacet_vw_spx c.1 c.mid_lt.ne' (c.lo_lt.trans c.mid_lt).ne' c.directions s
  have h1 := threeFacet_uw_spx c.1 c.mid_lt.ne' c.lo_lt.ne' c.directions s
  have h2 := threeFacet_uv_spx c.1 (c.lo_lt.trans c.mid_lt).ne' c.lo_lt.ne' c.directions s
  fin_cases e <;> constructor <;> apply Subtype.ext
  all_goals first
    | rw [qSquareSmallFacet_ordered _ c.lo_lt h0]
    | rw [qSquareLargeFacet_ordered _ c.lo_lt h0]
    | rw [qSquareSmallFacet_ordered _ (c.lo_lt.trans c.mid_lt) h1]
    | rw [qSquareLargeFacet_ordered _ (c.lo_lt.trans c.mid_lt) h1]
    | rw [qSquareSmallFacet_ordered _ c.mid_lt h2]
    | rw [qSquareLargeFacet_ordered _ c.mid_lt h2]
  all_goals first | rfl | exact qCubeFacet_comm _ c.mid_lt.ne s t | exact qCubeFacet_comm _ c.lo_lt.ne s t | exact qCubeFacet_comm _ (c.lo_lt.trans c.mid_lt).ne s t

end FiniteChains.Davis
