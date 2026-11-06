import Mathlib.Tactic

import RequestProject.QCubeEdgeSubdivision

/-! Actual coordinate facets of quotient cubes. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

  (c : QCube A)
  (v : V)
def qCubeFacet   (s : ZMod 2) : QCube A where
  spx := c.spx.erase v
  sgn := Function.update c.sgn v s
  isSimplex := isSimplex_subset A (Finset.erase_subset _ _) c.isSimplex
  sgn_eq_zero w hw := by
    classical simp_all [FiniteChains.Davis.QCube.sgn_eq_zero]

theorem qCubeFacet_le   (s : ZMod 2) (hv : v ∈ c.spx) :
    qCubeFacet c v s ≤ c := by
  refine ⟨Finset.erase_subset _ _, ?_⟩
  intro w hw
  have hne : w ≠ v := fun h => hw (h.symm ▸ hv)
  exact Function.update_of_ne hne _ _

theorem qCubeFacet_lt   (s : ZMod 2) (hv : v ∈ c.spx) :
    qCubeFacet c v s < c := by
  apply lt_of_le_of_ne (qCubeFacet_le c v s hv)
  intro h
  have hs  := congrArg QCube.spx h
  have hm  := hs.symm ▸ hv
  exact (Finset.notMem_erase v c.spx) hm

@[simp] theorem qCubeFacet_sgn_self   (s : ZMod 2) :
    (qCubeFacet c v s).sgn v = s := Function.update_self _ _ _

/-- Fixing two distinct directions gives the same actual face in either order. -/
theorem qCubeFacet_comm  {v w : V} (hne : v ≠ w) (s t : ZMod 2) :
    qCubeFacet (qCubeFacet c v s) w t = qCubeFacet (qCubeFacet c w t) v s := by
  apply QCube.ext'
  · change (c.spx.erase v).erase w = (c.spx.erase w).erase v
    ext x
    simp only [Finset.mem_erase]
    tauto
  · intro x _
    change Function.update (Function.update c.sgn v s) w t x =
      Function.update (Function.update c.sgn w t) v s x
    by_cases hxv : x = v
    · subst x
      simp [hne]
    · grind

theorem qCubeFacet_zero_of_singleton   (hs : c.spx = {v}) :
    qCubeFacet c v 0 = cubePositiveVertex c := by
  apply QCube.ext'
  · simp [qCubeFacet, cubePositiveVertex, hs]
  · intro w _
    change Function.update c.sgn v 0 w = c.sgn w
    by_cases h : w = v
    · classical simp_all [FiniteChains.Davis.QCube.sgn_eq_zero]
    · exact Function.update_of_ne h _ _

theorem qCubeFacet_one_of_singleton   (hs : c.spx = {v}) :
    qCubeFacet c v 1 = cubeNegativeVertex c v := by simp_all [qCubeFacet, cubeNegativeVertex]

/-- The strict one-cell subdivision agrees with the actual oriented cubical facets. -/
theorem oneCubeSubdivision_facet_boundary   (hs : c.spx = {v}) :
    Comb.bdry1 (strictOrderCx (QCube A)) (oneCubeSubdivision c v hs) =
      Finsupp.single (qCubeFacet c v 0) 1 - Finsupp.single (qCubeFacet c v 1) 1 := by
  rw [oneCubeSubdivision_boundary, qCubeFacet_zero_of_singleton c v hs,
    qCubeFacet_one_of_singleton c v hs]


/-- Positive facets are exactly the positive coordinate fixes used by the collapse. -/
theorem qCubeFacet_coordinate_zero   :
    qCubeToCoordinate (qCubeFacet c v 0) =
      Function.update (qCubeToCoordinate c) v CubeCoord.pos := by
  funext w
  by_cases h : w = v
  · simp_all [qCubeToCoordinate, qCubeFacet]
  · simp [qCubeToCoordinate, qCubeFacet, h]

/-- Negative facets are exactly the negative coordinate fixes used by the collapse. -/
theorem qCubeFacet_coordinate_one   :
    qCubeToCoordinate (qCubeFacet c v 1) =
      Function.update (qCubeToCoordinate c) v CubeCoord.neg := by
  funext w
  by_cases h : w = v
  · simp_all [qCubeToCoordinate, qCubeFacet]
  · simp [qCubeToCoordinate, qCubeFacet, h]

end FiniteChains.Davis
