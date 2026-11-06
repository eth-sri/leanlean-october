import RequestProject.TopologicalSingular.SimplexBoundaryGluing
import RequestProject.TopologicalSingular.SingularEdgeNullHomotopy
import RequestProject.Tac


bwd

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

theorem simplex_face_coordinate_succAbove i (z : Domain n) j :
    (stdSimplex.map (SimplexCategory.δ i) z).val (i.succAbove j) = z.val j := by
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove z.val) (i.succAbove j) = z.val j
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter]

theorem simplex_face_injective i :
    Function.Injective (stdSimplex.map (SimplexCategory.δ i) : Domain n → Domain (n + 1)) := by
  intro z w h
  apply Subtype.ext
  funext j
  have he := congrArg (·.val (i.succAbove j)) h
  grind [simplex_face_coordinate_succAbove]

/-- A point common to two different faces is on the boundary of each face. -/
theorem simplex_face_intersection_boundary i j (hij : i ≠ j)
    (z w : Domain n)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    z ∈ simplexBoundary n ∧ w ∈ simplexBoundary n := by
  have one (i j : Fin (n + 2)) (hij : i ≠ j) (z w : Domain n)
      (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
      z ∈ simplexBoundary n := by
    cases' Fin.exists_succAbove_eq hij.symm with k hk
    refine ⟨k, ?_⟩
    rw [← simplex_face_coordinate_succAbove i z k, hk, h]
    exact simplex_face_coordinate_zero j w
  tauto
