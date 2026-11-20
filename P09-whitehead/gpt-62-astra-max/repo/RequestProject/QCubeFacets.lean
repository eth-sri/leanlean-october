module

public import RequestProject.QCubeEdgeSubdivision

@[expose] public section

/-! Actual coordinate facets of quotient cubes. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

variable (c : QCube A)

variable (v : V) (s : ZMod 2)

def qCubeFacet : QCube A where
  spx := c.spx.erase v
  sgn := Function.update c.sgn v s
  isSimplex := isSimplex_subset A (Finset.erase_subset _ _) c.isSimplex
  sgn_eq_zero w hw := by
    have h := Finset.mem_erase.mp hw
    rw [Function.update_of_ne h.1]
    exact c.sgn_eq_zero w h.2

section

variable (hv : v ∈ c.spx)
include hv

theorem qCubeFacet_le :
    qCubeFacet c v s ≤ c := by
  refine ⟨Finset.erase_subset _ _, ?_⟩
  intro w hw
  have hne : w ≠ v := fun h => hw (h.symm ▸ hv)
  apply Function.update_of_ne <;> assumption

theorem qCubeFacet_lt :
    qCubeFacet c v s < c := by
  apply lt_of_le_of_ne (qCubeFacet_le c v s hv)
  intro h
  have hs : c.spx.erase v = c.spx := congrArg QCube.spx h
  simp_all

end

@[simp] theorem qCubeFacet_sgn_self :
    (qCubeFacet c v s).sgn v = s := Function.update_self _ _ _

/-- Fixing two distinct directions gives the same actual face in either order. -/
theorem qCubeFacet_comm {v w : V} (hne : v ≠ w) (s t : ZMod 2) :
    qCubeFacet (qCubeFacet c v s) w t = qCubeFacet (qCubeFacet c w t) v s := by
  apply QCube.ext'
  · change (c.spx.erase v).erase w = (c.spx.erase w).erase v
    grind
  · intro x _
    change Function.update (Function.update c.sgn v s) w t x =
      Function.update (Function.update c.sgn w t) v s x
    grind

variable (v : V)

section

variable (hs : c.spx = {v})
include hs

theorem qCubeFacet_zero_of_singleton :
    qCubeFacet c v 0 = cubePositiveVertex c := by
  apply QCube.ext'
  · simp [qCubeFacet, cubePositiveVertex, hs]
  · intro w _
    change Function.update c.sgn v 0 w = c.sgn w
    by_cases h : w = v
    · subst w
      rw [Function.update_self]
      exact (c.sgn_eq_zero v (by simp_all)).symm
    · simp_all

theorem qCubeFacet_one_of_singleton :
    qCubeFacet c v 1 = cubeNegativeVertex c v := by
  simp [qCubeFacet, cubeNegativeVertex, hs]

/-- The strict one-cell subdivision agrees with the actual oriented cubical facets. -/
theorem oneCubeSubdivision_facet_boundary :
    Comb.bdry1 _ (oneCubeSubdivision c v hs) =
      Finsupp.single (qCubeFacet c v 0) 1 - Finsupp.single (qCubeFacet c v 1) 1 := by
  simp_all [oneCubeSubdivision_boundary, qCubeFacet_zero_of_singleton, qCubeFacet_one_of_singleton]

end

/-- Positive facets are exactly the positive coordinate fixes used by the collapse. -/
theorem qCubeFacet_coordinate_zero :
    qCubeToCoordinate (qCubeFacet c v 0) =
      Function.update (qCubeToCoordinate c) v CubeCoord.pos := by
  funext w
  by_cases h : w = v
  · simp_all [qCubeToCoordinate, qCubeFacet]
  · simp [qCubeToCoordinate, qCubeFacet, h]

/-- Negative facets are exactly the negative coordinate fixes used by the collapse. -/
theorem qCubeFacet_coordinate_one :
    qCubeToCoordinate (qCubeFacet c v 1) =
      Function.update (qCubeToCoordinate c) v CubeCoord.neg := by
  funext w
  by_cases h : w = v
  · simp_all [qCubeToCoordinate, qCubeFacet]
  · simp [qCubeToCoordinate, qCubeFacet, h]

end FiniteChains.Davis
