module

public import RequestProject.QCubeCoordinateEquiv
public import RequestProject.StrictOrderChains

@[expose] public section

/-! Actual oriented edge subdivisions of quotient cubes. -/
open scoped Classical
set_option backward.isDefEq.respectTransparency false

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

variable (c : QCube A)

def cubePositiveVertex : QCube A :=
  ⟨∅, c.sgn, by simp [IsSimplex], fun _ h => by simp_all⟩

variable (v : V)

def cubeNegativeVertex : QCube A :=
  ⟨∅, Function.update c.sgn v 1, by simp [IsSimplex],
    fun _ h => by simp_all⟩

section

variable (hv : v ∈ c.spx)
include hv

theorem cubePositiveVertex_lt :
    cubePositiveVertex c < c := by
  refine lt_of_le_of_ne ⟨Finset.empty_subset _, fun _ _ => rfl⟩ ?_
  intro h
  have hs : c.spx = ∅ := (congrArg QCube.spx h).symm
  simp_all

theorem cubeNegativeVertex_lt :
    cubeNegativeVertex c v < c := by
  refine lt_of_le_of_ne ⟨Finset.empty_subset _, ?_⟩ ?_
  · intro w hw
    have hne : w ≠ v := fun h => hw (h.symm ▸ hv)
    apply Function.update_of_ne <;> assumption
  · intro h
    have hs : c.spx = ∅ := (congrArg QCube.spx h).symm
    simp_all

/-- The two strict radial half-edges in the chosen free direction. -/
noncomputable def cubeEdgeSubdivision :
    (strictOrderCx (QCube A)).E →₀ ℤ :=
  Finsupp.single ⟨(cubeNegativeVertex c v, c), cubeNegativeVertex_lt c v hv⟩ 1 -
    Finsupp.single ⟨(cubePositiveVertex c, c), cubePositiveVertex_lt c v hv⟩ 1

/-- This actual subdivision has the positive endpoint minus the negative endpoint as boundary. -/
theorem cubeEdgeSubdivision_boundary :
    Comb.bdry1 _ (cubeEdgeSubdivision c v hv) =
      Finsupp.single (cubePositiveVertex c) 1 - Finsupp.single (cubeNegativeVertex c v) 1 := by
  simp only [cubeEdgeSubdivision, map_sub, Comb.bdry1_single, one_smul]
  simp [strictOrderCx]

theorem cubeEndpoints_ne :
    cubeNegativeVertex c v ≠ cubePositiveVertex c := by
  simp_all [cubeNegativeVertex, cubePositiveVertex, (c.sgn_eq_zero v hv)]

end

variable (hs : c.spx = {v})

/-- For a genuine one-dimensional cube these are its actual oriented subdivided edges. -/
noncomputable def oneCubeSubdivision :=
  cubeEdgeSubdivision c v (by simp_all)

theorem oneCubeSubdivision_boundary :
    Comb.bdry1 _ (oneCubeSubdivision c v hs) =
      Finsupp.single (cubePositiveVertex c) 1 - Finsupp.single (cubeNegativeVertex c v) 1 :=
  by apply cubeEdgeSubdivision_boundary

theorem cubeEdgeSubdivision_ne_zero (hv : v ∈ c.spx) :
    cubeEdgeSubdivision c v hv ≠ 0 := by
  classical
  intro h
  have hb := congrArg (Comb.bdry1 (strictOrderCx (QCube A))) h
  rw [cubeEdgeSubdivision_boundary, map_zero] at hb
  have he := congrArg (fun z : QCube A →₀ ℤ => z (cubePositiveVertex c)) hb
  simp [cubeEndpoints_ne c v hv, Ne.symm _] at he

theorem cubeEdgeSubdivision_filter_tgt (d c : QCube A) (v : V) (hv : v ∈ d.spx) :
    (cubeEdgeSubdivision d v hv).filter
      (fun e : (strictOrderCx (QCube A)).E => e.1.2 = c) =
      if d = c then cubeEdgeSubdivision d v hv else 0 := by
  classical
  by_cases h : d = c <;> simp [cubeEdgeSubdivision, h, Finsupp.filter_single_of_pos, Finsupp.filter_single_of_neg]

end FiniteChains.Davis
