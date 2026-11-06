import RequestProject.TopologicalSingular.StickSimplex
import RequestProject.TopologicalSingular.BasedTriangleHomotopy
import RequestProject.TopologicalSingular.TriangleBasedNormalization


namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem simplex_face_eq_faceMap i (z : Domain n) :
    stdSimplex.map (SimplexCategory.δ i) z = faceMap i z := by
  apply Subtype.ext
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · exact (simplex_face_coordinate_zero i z).trans (faceMap_coe_same i z).symm
  · exact (simplex_face_coordinate_succAbove i z k).trans (by simp)

theorem stickSimplex_two_coordinates z :
    (stickSimplex 2 z).val =
      ![1 - (z 0 : ℝ), (z 0) * (1 - (z 1)), (z 0) * (z 1)] := by
  funext i
  fin_cases i
  · rfl
  · rfl
  · change (z 0) * ((z 1 : ℝ) * (stdSimplex.vertex (0)).val 0) = _
    simp

/-- The triangulation and stick-coordinate parametrizations have exactly the
same boundary, so their comparison requires no orientation convention. -/
theorem squareToTriangle_eq_stickSimplex_on_boundary z
    (hz : z ∈ Cube.boundary (Fin 2)) : squareToTriangle z = stickSimplex 2 z := by
  obtain ⟨i, hi⟩ := hz
  fin_cases i <;> rcases hi with hi | hi
  all_goals
    dsimp at hi
    apply Subtype.ext
    rw [stickSimplex_two_coordinates]
    funext j
    fin_cases j
    all_goals
      simp [squareToTriangle, hi, (z 0).property.1, (z 0).property.2,
        (z 1).property.1, (z 1).property.2]

noncomputable def basedTriangleStickSquare (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    GenLoop (Fin 2) X x :=
  ⟨tau.comp (stickSimplex 2), by
    intro z hz
    cases' stickSimplex_mem_bdry 2 z hz with i hi
    exact basedTriangle_eq_of_zero_coordinate tau h _ i hi⟩

theorem basedTriangleSquare_homotopic_stick (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    GenLoop.Homotopic (basedTriangleSquare tau h) (basedTriangleStickSquare tau h) :=
  ⟨(simplexLinearHomotopyRel squareToTriangle _ _
    squareToTriangle_eq_stickSimplex_on_boundary).compContinuousMap tau⟩

theorem basedTriangleStickSquare_pi2_eq tau
    h :
    (Quotient.mk _ (basedTriangleStickSquare tau h) : HomotopyGroup (Fin 2) X x) =
      Quotient.mk _ (basedTriangleSquare tau h) :=
  (Quotient.sound (basedTriangleSquare_homotopic_stick tau h)).symm
