import RequestProject.QCubeSquareBoundary
import RequestProject.StrictTopConeChains
import RequestProject.Tac
noncomputable section


/-! Actual strict barycentric subdivisions of quotient two-cubes. -/
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def cubeLowerIncl (c : QCube A) :
    Hom (strictOrderCx (Set.Iio c)) (strictOrderCx (QCube A)) :=
  strictOrderCxMap Subtype.val (by tauto)

def lowerFacetEdgeChain (c d : QCube A) (hd : d < c)
    v (hv : v ∈ d.spx) : (strictOrderCx (Set.Iio c)).E →₀ ℤ :=
  Finsupp.single ⟨(⟨cubeNegativeVertex d v, (cubeNegativeVertex_lt d v hv).trans hd⟩,
    ⟨d, hd⟩), cubeNegativeVertex_lt d v hv⟩ 1 -
  Finsupp.single ⟨(⟨cubePositiveVertex d, (cubePositiveVertex_lt d v hv).trans hd⟩,
    ⟨d, hd⟩), cubePositiveVertex_lt d v hv⟩ 1

theorem lowerFacetEdgeChain_projection (c d : QCube A) hd
    v hv :
    chain1 (cubeLowerIncl c) (lowerFacetEdgeChain c d hd v hv) =
      cubeEdgeSubdivision d v hv := by
  simp [lowerFacetEdgeChain, map_sub, chain1, cubeLowerIncl, strictOrderCxMap, cubeEdgeSubdivision, Finsupp.lmapDomain_apply]

def lowerSquareEdgeBoundary (c : QCube A) v w (hne : v ≠ w)
    (hs : c.spx = {v, w}) :=
  lowerFacetEdgeChain c _
    (qCubeFacet_lt c w 0 (by simp_all)) v
    (by simp [squareFacet_v_spx c hne hs 0]) -
  lowerFacetEdgeChain c _
    (qCubeFacet_lt c w 1 (by simp_all)) v
    (by simp [squareFacet_v_spx c hne hs 1]) -
  lowerFacetEdgeChain c _
    (qCubeFacet_lt c v 0 (by simp_all)) w
    (by simp [squareFacet_w_spx c hne hs 0]) +
  lowerFacetEdgeChain c _
    (qCubeFacet_lt c v 1 (by simp_all)) w
    (by simp [squareFacet_w_spx c hne hs 1])

theorem lowerSquareEdgeBoundary_projection (c : QCube A) v w hne
    hs :
    chain1 (cubeLowerIncl c) (lowerSquareEdgeBoundary c v w hne hs) =
      cubeSquareEdgeBoundary c v w hne hs := by
  simp [lowerSquareEdgeBoundary, map_add, map_sub, lowerFacetEdgeChain_projection]
  rfl

theorem lowerSquareEdgeBoundary_cycle (c : QCube A) v w hne
    hs :
    Comb.bdry1 (strictOrderCx (Set.Iio c)) (lowerSquareEdgeBoundary c v w hne hs) = 0 := by
  apply Finsupp.mapDomain_injective (f := fun x => x.val) Subtype.val_injective
  change chain0 (cubeLowerIncl c) (Comb.bdry1 _
    (lowerSquareEdgeBoundary c v w hne hs)) = chain0 (cubeLowerIncl c) 0
  simp [← bdry1_chain1, lowerSquareEdgeBoundary_projection, cubeSquareEdgeBoundary_cycle, map_zero]

/-- The actual two-cube is filled by its eight nondegenerate barycentric triangles. -/
def cubeSquareSubdivision (c : QCube A) v w (hne : v ≠ w)
    (hs : c.spx = {v, w}) : (strictOrderCx (QCube A)).F →₀ ℤ :=
  strictTopConeEdgeChain Subtype.val (by tauto) c (by simp)
    (lowerSquareEdgeBoundary c v w hne hs)

/-- Its actual strict cellular boundary is precisely the oriented four-facet edge chain. -/
theorem cubeSquareSubdivision_boundary c v w hne
    hs :
    Comb.bdry2 (strictOrderCx (QCube A)) (cubeSquareSubdivision c v w hne hs) =
      cubeSquareEdgeBoundary c v w hne hs := by
  rwd [cubeSquareSubdivision, strictTopConeEdgeChain_cycle_boundary _ _ _ _ _
    (lowerSquareEdgeBoundary_cycle c v w hne hs)]
  exact lowerSquareEdgeBoundary_projection c v w hne hs

/-- The square subdivision uses only triangles whose largest cell is that square. -/
theorem cubeSquareSubdivision_eq_zero_off_top c v w hne
    hs (t : (strictOrderCx (QCube A)).F) (ht : t.1.2.2 ≠ c) :
    cubeSquareSubdivision c v w hne hs t = 0 :=
  strictTopConeEdgeChain_eq_zero_off_top _ _ _ _ _ t ht
