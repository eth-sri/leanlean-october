module

public import RequestProject.TopologicalSingular.StickSimplex
public import RequestProject.TopologicalSingular.BasedTriangleHurewicz
public import RequestProject.TopologicalSingular.SimplexLinearHomotopy
public import RequestProject.TopologicalSingular.SimplexPrismRetraction
public import RequestProject.TopologicalSingular.TriangleBasedNormalization

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {x : X}

theorem simplex_face_eq_faceMap {n : ℕ} (i : Fin (n + 2)) (z : Domain n) :
    stdSimplex.map (SimplexCategory.δ i) z = faceMap i z :=
  Subtype.ext (simplex_map_succAbove i z)

theorem stickSimplex_two_coordinates (z : Fin 2 → I) :
    (stickSimplex 2 z).val =
      ![1 - (z 0 : ℝ), (z 0 : ℝ) * (1 - (z 1 : ℝ)), (z 0 : ℝ) * (z 1 : ℝ)] := by
  funext i
  fin_cases i
  · exact stickSimplex_succ_zero 1 z
  · tauto
  · change (z 0) * ((z 1) * (stdSimplex.vertex 0 : Domain 0).val 0) = _
    simp

/-- The triangulation and stick-coordinate parametrizations have exactly the
same boundary, so their comparison requires no orientation convention. -/
theorem squareToTriangle_eq_stickSimplex_on_boundary (z : Fin 2 → I)
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
        (z 1).property.1, (z 1).property.2,
        sub_nonneg.mpr (z 1).property.2, sub_nonpos.mpr (z 0).property.2]

noncomputable def basedTriangleStickSquare (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    GenLoop (Fin 2) X x :=
  ⟨tau.comp (stickSimplex 2), by
    intro z hz
    obtain ⟨i, hi⟩ := stickSimplex_mem_bdry 2 z hz
    exact basedTriangle_eq_of_zero_coordinate tau h _ i hi⟩

theorem basedTriangleSquare_homotopic_stick (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    GenLoop.Homotopic (basedTriangleSquare tau h) (basedTriangleStickSquare tau h) :=
  ⟨(simplexLinearHomotopyRel squareToTriangle (stickSimplex 2) (Cube.boundary (Fin 2))
    squareToTriangle_eq_stickSimplex_on_boundary).compContinuousMap tau⟩

theorem basedTriangleStickSquare_pi2_eq (tau : Simplex X 2)
    (h : ∀ i : Fin 3, face i tau = ContinuousMap.const (Domain 1) x) :
    (Quotient.mk _ (basedTriangleStickSquare tau h) : HomotopyGroup (Fin 2) X x) =
      Quotient.mk _ (basedTriangleSquare tau h) :=
  (Quotient.sound (basedTriangleSquare_homotopic_stick tau h)).symm

end FiniteChains.TopologicalSingular
