module

public import RequestProject.TopologicalSingular.StickSimplex
public import RequestProject.TopologicalSingular.BasedTriangleHurewicz
public import RequestProject.TopologicalSingular.SimplexLinearHomotopy
public import RequestProject.TopologicalSingular.TriangleBasedNormalization

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem simplex_face_eq_faceMap {n : ℕ} (i : Fin _) (z : Domain n) :
    stdSimplex.map (SimplexCategory.δ i) z = faceMap i z := by
  apply Subtype.ext
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp_all [simplex_face_coordinate_zero, faceMap_coe_same]
  · simp_all [simplex_face_coordinate_succAbove, faceMap_coe_succAbove]

variable (z : Fin 2 → I)

theorem stickSimplex_two_coordinates :
    (stickSimplex 2 z).val =
      ![1 - (z 0 : ℝ), (z 0) * (1 - (z 1)), (z 0) * (z 1)] := by
  funext i
  fin_cases i
  · exact stickSimplex_succ_zero 1 z
  · rfl
  · change (z 0) * ((z 1) * (stdSimplex.vertex _ : Domain 0).val 0) = _
    simp

/-- The triangulation and stick-coordinate parametrizations have exactly the
same boundary, so their comparison requires no orientation convention. -/
theorem squareToTriangle_eq_stickSimplex_on_boundary
    (hz : z ∈ Cube.boundary _) : squareToTriangle z = stickSimplex 2 z := by
  obtain ⟨i, hi⟩ := hz
  fin_cases i <;> rcases hi with hi | hi
  all_goals
    dsimp at hi
    apply Subtype.ext
    rw [stickSimplex_two_coordinates]
    all_goals
      simp [squareToTriangle, hi, (z 0).property.1, (z 0).property.2,
        (z 1).property.1, (z 1).property.2,
        sub_nonneg.mpr (z 1).property.2, sub_nonpos.mpr (z 0).property.2]

variable (tau : Simplex X 2) (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x)

noncomputable def basedTriangleStickSquare :
    GenLoop (Fin 2) X x :=
  ⟨tau.comp (stickSimplex 2), by
    intro z hz
    obtain ⟨i, hi⟩ := stickSimplex_mem_bdry 2 z hz
    apply basedTriangle_eq_of_zero_coordinate <;> assumption⟩

theorem basedTriangleSquare_homotopic_stick :
    GenLoop.Homotopic (basedTriangleSquare tau h) (basedTriangleStickSquare tau h) :=
  ⟨(simplexLinearHomotopyRel squareToTriangle _ _
    squareToTriangle_eq_stickSimplex_on_boundary).compContinuousMap tau⟩

theorem basedTriangleStickSquare_pi2_eq :
    (Quotient.mk _ (basedTriangleStickSquare tau h) : HomotopyGroup (Fin 2) X x) =
      Quotient.mk _ (basedTriangleSquare tau h) :=
  (Quotient.sound (basedTriangleSquare_homotopic_stick tau h)).symm

end FiniteChains.TopologicalSingular
