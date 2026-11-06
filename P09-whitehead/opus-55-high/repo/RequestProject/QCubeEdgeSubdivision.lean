import RequestProject.QCubeCoordinateEquiv
import RequestProject.StrictOrderChains
import RequestProject.Tac
noncomputable section


/-! Actual oriented edge subdivisions of quotient cubes. -/
open scoped Classical

bwd

namespace FiniteChains.Davis
open RACG Mirror Comb
variable {V : Type} [DecidableEq V] {A : CommRel V}

def cubePositiveVertex (c : QCube A) : QCube A :=
  ⟨∅, c.sgn, by tauto, by simp⟩

def cubeNegativeVertex (c : QCube A) (v : V) : QCube A :=
  ⟨∅, Function.update c.sgn v 1, by tauto,
    by simp⟩

theorem cubePositiveVertex_lt (c : QCube A) v (hv : v ∈ c.spx) :
    cubePositiveVertex c < c := by
  refine lt_of_le_of_ne ⟨Finset.empty_subset _, fun _ _ => rfl⟩ ?_
  intro h
  have hs : c.spx = ∅ := (congrArg QCube.spx h).symm
  simp_all

theorem cubeNegativeVertex_lt (c : QCube A) v (hv : v ∈ c.spx) :
    cubeNegativeVertex c v < c := by
  refine lt_of_le_of_ne ⟨Finset.empty_subset _, ?_⟩ ?_
  · intro w hw
    have hne : w ≠ v := by grind
    exact Function.update_of_ne hne _ _
  · intro h
    have hs : c.spx = ∅ := (congrArg QCube.spx h).symm
    simp_all

/-- The two strict radial half-edges in the chosen free direction. -/
def cubeEdgeSubdivision (c : QCube A) v (hv : v ∈ c.spx) :
    (strictOrderCx (QCube A)).E →₀ ℤ :=
  Finsupp.single ⟨(cubeNegativeVertex c v, c), cubeNegativeVertex_lt c v hv⟩ 1 -
    Finsupp.single ⟨(cubePositiveVertex c, c), cubePositiveVertex_lt c v hv⟩ 1

/-- This actual subdivision has the positive endpoint minus the negative endpoint as boundary. -/
theorem cubeEdgeSubdivision_boundary c v hv :
    Comb.bdry1 (strictOrderCx (QCube A)) (cubeEdgeSubdivision c v hv) =
      Finsupp.single (cubePositiveVertex c) 1 - Finsupp.single (cubeNegativeVertex c v) 1 := by
  simp [cubeEdgeSubdivision, map_sub, Comb.bdry1_single, one_smul]
  simp only [strictOrderCx]
  abel

theorem cubeEndpoints_ne (c : QCube A) v (hv : v ∈ c.spx) :
    cubeNegativeVertex c v ≠ cubePositiveVertex c := by
  intro h
  have he := congrArg (·.sgn v) h
  have hv0 := c.sgn_eq_zero v hv
  simp [cubeNegativeVertex, cubePositiveVertex, hv0] at he

/-- For a genuine one-dimensional cube these are its actual oriented subdivided edges. -/
def oneCubeSubdivision (c : QCube A) v (hs : c.spx = {v}) :=
  cubeEdgeSubdivision c v (by simp_all)

theorem oneCubeSubdivision_boundary c v hs :
    Comb.bdry1 (strictOrderCx (QCube A)) (oneCubeSubdivision c v hs) =
      Finsupp.single (cubePositiveVertex c) 1 - Finsupp.single (cubeNegativeVertex c v) 1 :=
  cubeEdgeSubdivision_boundary c v _

theorem cubeEdgeSubdivision_ne_zero (c : QCube A) v hv :
    cubeEdgeSubdivision c v hv ≠ 0 := by
  classical
  intro h
  have hb := congrArg (Comb.bdry1 (strictOrderCx (QCube A))) h
  rw [cubeEdgeSubdivision_boundary, map_zero] at hb
  have he := congrArg (· (cubePositiveVertex c)) hb
  simp [cubeEndpoints_ne c v hv] at he

theorem cubeEdgeSubdivision_filter_tgt d c v hv :
    (cubeEdgeSubdivision d v hv).filter
      (fun e : (strictOrderCx (QCube A)).E => e.1.2 = c) =
      if d = c then cubeEdgeSubdivision d v hv else 0 := by
  classical
  by_cases h : d = c <;> simp [cubeEdgeSubdivision, h, Finsupp.filter_single_of_pos, Finsupp.filter_single_of_neg]
