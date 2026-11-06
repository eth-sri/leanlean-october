module

public import RequestProject.QCubeSquareBoundary
public import RequestProject.StrictTopConeChains

@[expose] public section

/-! Actual strict barycentric subdivisions of quotient two-cubes. -/
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def cubeLowerIncl (c : QCube A) :
    Hom (strictOrderCx (Set.Iio c)) (strictOrderCx (QCube A)) :=
  strictOrderCxMap Subtype.val (fun _ _ h => h)

noncomputable def lowerFacetEdgeChain (c d : QCube A) (hd : d < c)
    (v : V) (hv : v ∈ d.spx) : (strictOrderCx (Set.Iio c)).E →₀ ℤ :=
  Finsupp.single ⟨(⟨cubeNegativeVertex d v, (cubeNegativeVertex_lt d v hv).trans hd⟩,
    ⟨d, hd⟩), cubeNegativeVertex_lt d v hv⟩ 1 -
  Finsupp.single ⟨(⟨cubePositiveVertex d, (cubePositiveVertex_lt d v hv).trans hd⟩,
    ⟨d, hd⟩), cubePositiveVertex_lt d v hv⟩ 1

theorem lowerFacetEdgeChain_projection (c d : QCube A) (hd : d < c)
    (v : V) (hv : v ∈ d.spx) :
    chain1 (cubeLowerIncl c) (lowerFacetEdgeChain c d hd v hv) =
      cubeEdgeSubdivision d v hv := by
  erw [lowerFacetEdgeChain, map_sub]
  simp [chain1, cubeLowerIncl, strictOrderCxMap, cubeEdgeSubdivision, Finsupp.lmapDomain_apply]

noncomputable def lowerSquareEdgeBoundary (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) : (strictOrderCx (Set.Iio c)).E →₀ ℤ :=
  lowerFacetEdgeChain c (qCubeFacet c w 0)
    (qCubeFacet_lt c w 0 (by erw [hs]; simp)) v
    (by erw [squareFacet_v_spx c hne hs 0]; simp) -
  lowerFacetEdgeChain c (qCubeFacet c w 1)
    (qCubeFacet_lt c w 1 (by erw [hs]; simp)) v
    (by erw [squareFacet_v_spx c hne hs 1]; simp) -
  lowerFacetEdgeChain c (qCubeFacet c v 0)
    (qCubeFacet_lt c v 0 (by erw [hs]; simp)) w
    (by erw [squareFacet_w_spx c hne hs 0]; simp) +
  lowerFacetEdgeChain c (qCubeFacet c v 1)
    (qCubeFacet_lt c v 1 (by erw [hs]; simp)) w
    (by erw [squareFacet_w_spx c hne hs 1]; simp)

theorem lowerSquareEdgeBoundary_projection (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) :
    chain1 (cubeLowerIncl c) (lowerSquareEdgeBoundary c v w hne hs) =
      cubeSquareEdgeBoundary c v w hne hs := by
  simp only [lowerSquareEdgeBoundary, map_add, map_sub, lowerFacetEdgeChain_projection]
  rfl

theorem lowerSquareEdgeBoundary_cycle (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) :
    Comb.bdry1 (strictOrderCx (Set.Iio c)) (lowerSquareEdgeBoundary c v w hne hs) = 0 := by
  apply Finsupp.mapDomain_injective (f := fun x : Set.Iio c => x.val) Subtype.val_injective
  change chain0 (cubeLowerIncl c) (Comb.bdry1 (strictOrderCx (Set.Iio c))
    (lowerSquareEdgeBoundary c v w hne hs)) = chain0 (cubeLowerIncl c) 0
  erw [← bdry1_chain1, lowerSquareEdgeBoundary_projection, cubeSquareEdgeBoundary_cycle,
    map_zero]

/-- The actual two-cube is filled by its eight nondegenerate barycentric triangles. -/
noncomputable def cubeSquareSubdivision (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) : (strictOrderCx (QCube A)).F →₀ ℤ :=
  strictTopConeEdgeChain Subtype.val (fun _ _ h => h) c (fun x : Set.Iio c => x.2)
    (lowerSquareEdgeBoundary c v w hne hs)

/-- Its actual strict cellular boundary is precisely the oriented four-facet edge chain. -/
theorem cubeSquareSubdivision_boundary (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) :
    Comb.bdry2 (strictOrderCx (QCube A)) (cubeSquareSubdivision c v w hne hs) =
      cubeSquareEdgeBoundary c v w hne hs := by
  erw [cubeSquareSubdivision, strictTopConeEdgeChain_cycle_boundary _ _ _ _ _
    (lowerSquareEdgeBoundary_cycle c v w hne hs)]
  exact lowerSquareEdgeBoundary_projection c v w hne hs

/-- The square subdivision uses only triangles whose largest cell is that square. -/
theorem cubeSquareSubdivision_eq_zero_off_top (c : QCube A) (v w : V) (hne : v ≠ w)
    (hs : c.spx = {v, w}) (t : (strictOrderCx (QCube A)).F) (ht : t.1.2.2 ≠ c) :
    cubeSquareSubdivision c v w hne hs t = 0 :=
  strictTopConeEdgeChain_eq_zero_off_top _ _ _ _ _ t ht
