module

public import RequestProject.TopologicalSingular.SimplexBoundaryGluing
public import RequestProject.TopologicalSingular.SingularEdgeNullHomotopy

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

variable (i : Fin (n + 2))

theorem simplex_face_coordinate_succAbove (z : Domain n) (j : Fin _) :
    (stdSimplex.map (SimplexCategory.δ i) z).val (i.succAbove j) = z.val j := by
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove z.val) _ = z.val j
  simp [FunOnFinite.linearMap_apply_apply, Finset.sum_filter]

theorem simplex_face_injective :
    Function.Injective (stdSimplex.map (SimplexCategory.δ i) : Domain n → Domain (n + 1)) := by
  intro z w h
  apply Subtype.ext
  funext j
  simpa only [simplex_face_coordinate_succAbove] using (congrArg (fun v : Domain _ => v.val (i.succAbove j)) h)

/-- A point common to two different faces is on the boundary of each face. -/
theorem simplex_face_intersection_boundary (i j : Fin _) (hij : i ≠ j)
    (z w : Domain n)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    z ∈ simplexBoundary n ∧ w ∈ simplexBoundary n := by
  have one (i j : Fin _) (hij : i ≠ j) (z w : Domain n)
      (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
      z ∈ simplexBoundary n := by
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    refine ⟨k, ?_⟩
    rw [← simplex_face_coordinate_succAbove i z k, hk, h]
    exact simplex_face_coordinate_zero j w
  grind

end FiniteChains.TopologicalSingular
