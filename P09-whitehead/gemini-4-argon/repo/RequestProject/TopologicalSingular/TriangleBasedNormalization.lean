module

public import RequestProject.TopologicalSingular.SimplexBoundaryGluing
public import RequestProject.TopologicalSingular.SingularEdgeNullHomotopy

@[expose] public section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] {n : ℕ}

theorem simplex_face_coordinate_succAbove (i : Fin (n + 2)) (z : Domain n) (j : Fin (n + 1)) :
    (stdSimplex.map (SimplexCategory.δ i) z).val (i.succAbove j) = z.val j := by
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove z.val) (i.succAbove j) = z.val j
  rw [FunOnFinite.linearMap_apply_apply]
  simp [Finset.sum_filter]

theorem simplex_face_injective (i : Fin (n + 2)) :
    Function.Injective (stdSimplex.map (SimplexCategory.δ i) : Domain n → Domain (n + 1)) := by
  intro z w h
  apply Subtype.ext
  funext j
  have he := congrArg (fun v : Domain (n + 1) => v.val (i.succAbove j)) h
  simpa only [simplex_face_coordinate_succAbove] using he

/-- A point common to two different faces is on the boundary of each face. -/
theorem simplex_face_intersection_boundary (i j : Fin (n + 2)) (hij : i ≠ j)
    (z w : Domain n)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    z ∈ simplexBoundary n ∧ w ∈ simplexBoundary n := by
  have one (i j : Fin (n + 2)) (hij : i ≠ j) (z w : Domain n)
      (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
      z ∈ simplexBoundary n := by
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hij.symm
    refine ⟨k, ?_⟩
    rw [← simplex_face_coordinate_succAbove i z k, hk, h]
    exact simplex_face_coordinate_zero j w
  exact ⟨one i j hij z w h, one j i hij.symm w z h.symm⟩

end FiniteChains.TopologicalSingular
