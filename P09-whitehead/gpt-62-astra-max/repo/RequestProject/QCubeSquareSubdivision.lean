module

public import RequestProject.QCubeSquareBoundary
public import RequestProject.StrictTopConeChains

@[expose] public section

/-! Actual strict barycentric subdivisions of quotient two-cubes. -/
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def cubeLowerIncl (c : QCube A) :
    Hom (strictOrderCx (Set.Iio c)) (strictOrderCx (QCube A)) :=
  strictOrderCxMap Subtype.val (fun _ _ h => h)

variable (c d : QCube A) (hd : d < c) (v : V) (hv : v ∈ d.spx)

def lowerFacetEdgeChain : (strictOrderCx (Set.Iio c)).E →₀ ℤ :=
  Finsupp.single ⟨(⟨cubeNegativeVertex d v, (cubeNegativeVertex_lt d v hv).trans hd⟩,
    ⟨d, hd⟩), cubeNegativeVertex_lt d v hv⟩ 1 -
  Finsupp.single ⟨(⟨cubePositiveVertex d, (cubePositiveVertex_lt d v hv).trans hd⟩,
    ⟨d, hd⟩), cubePositiveVertex_lt d v hv⟩ 1

theorem lowerFacetEdgeChain_projection :
    chain1 (cubeLowerIncl c) (lowerFacetEdgeChain c d hd v hv) =
      cubeEdgeSubdivision d v hv := by
  simp [lowerFacetEdgeChain, map_sub, chain1, cubeLowerIncl, strictOrderCxMap, cubeEdgeSubdivision, Finsupp.lmapDomain_apply]

variable (c : QCube A) (v w : V) (hne : v ≠ w) (hs : c.spx = {v, w})

def lowerSquareEdgeBoundary :=
  lowerFacetEdgeChain c _
    (qCubeFacet_lt c w 0 (by simp_all)) v
    (by erw [squareFacet_v_spx c hne hs 0]; simp) -
  lowerFacetEdgeChain c _
    (qCubeFacet_lt c w 1 (by simp_all)) v
    (by erw [squareFacet_v_spx c hne hs 1]; simp) -
  lowerFacetEdgeChain c _
    (qCubeFacet_lt c v 0 (by simp_all)) w
    (by grind [squareFacet_w_spx]) +
  lowerFacetEdgeChain c _
    (qCubeFacet_lt c v 1 (by simp_all)) w
    (by grind [squareFacet_w_spx])

theorem lowerSquareEdgeBoundary_projection :
    chain1 (cubeLowerIncl c) (lowerSquareEdgeBoundary c v w hne hs) =
      cubeSquareEdgeBoundary c v w hne hs := by
  simp only [lowerSquareEdgeBoundary, map_add, map_sub, lowerFacetEdgeChain_projection]
  rfl

theorem lowerSquareEdgeBoundary_cycle :
    Comb.bdry1 _ (lowerSquareEdgeBoundary c v w hne hs) = 0 := by
  apply Finsupp.mapDomain_injective (f := fun x : Set.Iio c => x.val) Subtype.val_injective
  change chain0 (cubeLowerIncl c) _ = chain0 (cubeLowerIncl c) 0
  erw [← bdry1_chain1, lowerSquareEdgeBoundary_projection, cubeSquareEdgeBoundary_cycle,
    map_zero]

/-- The actual two-cube is filled by its eight nondegenerate barycentric triangles. -/
def cubeSquareSubdivision :=
  strictTopConeEdgeChain Subtype.val (fun _ _ h => h) c (fun x : Set.Iio c => x.2)
    (lowerSquareEdgeBoundary c v w hne hs)

/-- Its actual strict cellular boundary is precisely the oriented four-facet edge chain. -/
theorem cubeSquareSubdivision_boundary :
    Comb.bdry2 _ (cubeSquareSubdivision c v w hne hs) =
      cubeSquareEdgeBoundary c v w hne hs := by
  erw [cubeSquareSubdivision, strictTopConeEdgeChain_cycle_boundary _ _ _ _ _
    (lowerSquareEdgeBoundary_cycle c v w hne hs)]
  apply lowerSquareEdgeBoundary_projection

/-- The square subdivision uses only triangles whose largest cell is that square. -/
theorem cubeSquareSubdivision_eq_zero_off_top (t : (strictOrderCx (QCube A)).F) (ht : t.1.2.2 ≠ c) :
    cubeSquareSubdivision c v w hne hs t = 0 :=
  by solve_by_elim [strictTopConeEdgeChain_eq_zero_off_top]

end FiniteChains.Davis
