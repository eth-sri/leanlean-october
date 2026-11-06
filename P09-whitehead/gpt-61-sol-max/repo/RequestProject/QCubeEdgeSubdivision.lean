import Mathlib.Tactic

import RequestProject.QCubeCoordinateEquiv
import RequestProject.StrictOrderChains

/-! Actual oriented edge subdivisions of quotient cubes. -/
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

  (c : QCube A)
def cubePositiveVertex  : QCube A :=
  ⟨∅, c.sgn, by simp [IsSimplex], fun _ h => by simp at h⟩

variable (v : V)
def cubeNegativeVertex   : QCube A :=
  ⟨∅, Function.update c.sgn v 1, by simp [IsSimplex],
    fun _ h => by simp at h⟩

theorem cubePositiveVertex_lt   (hv : v ∈ c.spx) :
    cubePositiveVertex c < c := by
  refine lt_of_le_of_ne ⟨Finset.empty_subset _, fun _ _ => rfl⟩ ?_
  intro h
  have hs : c.spx = ∅ := (congrArg QCube.spx h).symm
  simp [hs] at hv

theorem cubeNegativeVertex_lt   (hv : v ∈ c.spx) :
    cubeNegativeVertex c v < c := by
  refine lt_of_le_of_ne ⟨Finset.empty_subset _, ?_⟩ ?_
  · intro w hw
    have hne : w ≠ v := fun h => hw (h.symm ▸ hv)
    exact Function.update_of_ne hne _ _
  · intro h
    have hs : c.spx = ∅ := (congrArg QCube.spx h).symm
    simp [hs] at hv

/-- The two strict radial half-edges in the chosen free direction. -/
noncomputable def cubeEdgeSubdivision   (hv : v ∈ c.spx) :
    (strictOrderCx (QCube A)).E →₀ ℤ :=
  Finsupp.single ⟨(cubeNegativeVertex c v, c), cubeNegativeVertex_lt c v hv⟩ 1 -
    Finsupp.single ⟨(cubePositiveVertex c, c), cubePositiveVertex_lt c v hv⟩ 1

/-- This actual subdivision has the positive endpoint minus the negative endpoint as boundary. -/
theorem cubeEdgeSubdivision_boundary   (hv : v ∈ c.spx) :
    Comb.bdry1 (strictOrderCx (QCube A)) (cubeEdgeSubdivision c v hv) =
      Finsupp.single (cubePositiveVertex c) 1 - Finsupp.single (cubeNegativeVertex c v) 1 := by
  simp only [cubeEdgeSubdivision, map_sub, Comb.bdry1_single]
  simp only [strictOrderCx]
  abel

theorem cubeEndpoints_ne   (hv : v ∈ c.spx) :
    cubeNegativeVertex c v ≠ cubePositiveVertex c := by
  classical simp_all [FiniteChains.Davis.QCube.sgn_eq_zero, cubeNegativeVertex, cubePositiveVertex]

/-- For a genuine one-dimensional cube these are its actual oriented subdivided edges. -/
noncomputable def oneCubeSubdivision   (hs : c.spx = {v})  :=
  cubeEdgeSubdivision c v (by rw [hs]; simp)

theorem oneCubeSubdivision_boundary   (hs : c.spx = {v}) :
    Comb.bdry1 (strictOrderCx (QCube A)) (oneCubeSubdivision c v hs) =
      Finsupp.single (cubePositiveVertex c) 1 - Finsupp.single (cubeNegativeVertex c v) 1 :=
  cubeEdgeSubdivision_boundary c v _

theorem cubeEdgeSubdivision_ne_zero   (hv : v ∈ c.spx) :
    cubeEdgeSubdivision c v hv ≠ 0 := by
  intro h
  have hb := congrArg (Comb.bdry1 (strictOrderCx (QCube A))) h
  rw [cubeEdgeSubdivision_boundary, map_zero] at hb
  have he := congrArg (fun z : QCube A →₀ ℤ => z (cubePositiveVertex c)) hb
  simp [Ne.symm (cubeEndpoints_ne c v hv)] at he

theorem cubeEdgeSubdivision_filter_tgt (d c : QCube A) (v : V) (hv : v ∈ d.spx) :
    (cubeEdgeSubdivision d v hv).filter
      (fun e : (strictOrderCx (QCube A)).E => e.1.2 = c) =
      if d = c then cubeEdgeSubdivision d v hv else 0 := by
  by_cases h : d = c <;> simp [cubeEdgeSubdivision, h]

end FiniteChains.Davis
