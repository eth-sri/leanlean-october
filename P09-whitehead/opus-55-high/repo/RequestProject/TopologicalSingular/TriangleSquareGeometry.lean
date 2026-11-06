import RequestProject.TopologicalSingular.SquareSingularChains


namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology

/-- A zero barycentric coordinate identifies an actual point of that face. -/
theorem domain_zero_coordinate_face (z : Domain (n + 1)) (i : Fin (n + 2))
    (hi : z.val i = 0) : ∃ w : Domain n, stdSimplex.map (SimplexCategory.δ i) w = z := by
  let w : Domain n := ⟨fun j => z.val (i.succAbove j), fun j => z.property.1 _, by
    have hs := z.property.2
    simp_all [Fin.sum_univ_succAbove _ i, hi, zero_add]⟩
  refine ⟨w, ?_⟩
  apply Subtype.ext
  funext k
  change (FunOnFinite.linearMap ℝ ℝ i.succAbove w.val) k = z.val k
  rw [FunOnFinite.linearMap_apply_apply]
  by_cases hk : k = i
  · simp_all
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hk
    simp [w, Finset.sum_filter]

/-- Collapse the upper triangle of the square onto an edge of the standard
triangle. On the lower triangle this map is exactly the identity simplex. -/
noncomputable def squareToTriangle : C((Fin 2 → I), Domain 2) where
  toFun z := ⟨![1 - (z 0 : ℝ), max ((z 0 : ℝ) - z 1) 0, min (z 0 : ℝ) (z 1 : ℝ)], by
    constructor
    · intro i
      fin_cases i
      · exact sub_nonneg.mpr (z 0).property.2
      · simp
      · exact le_min (z 0).property.1 (z 1).property.1
    · rw [Fin.sum_univ_three]
      change 1 - (z 0 : ℝ) + max ((z 0 : ℝ) - z 1) 0 + min (z 0 : ℝ) (z 1 : ℝ) = 1
      grind⟩
  continuous_toFun := by
    fun_prop

theorem squareToTriangle_triangle1 z : squareToTriangle (cubeTriangle1 z) = z := by
  have hs := (Fin.sum_univ_three z.val).symm.trans z.property.2
  have h : z.val 2 ≤ 1 - z.val 0 := by linarith [z.property.1 1]
  apply Subtype.ext
  change ![1 - (1 - z.val 0), max ((1 - z.val 0) - z.val 2) 0,
    min (1 - z.val 0) (z.val 2)] = z.val
  funext i
  fin_cases i
  · simp
  · change max ((1 - z.val 0) - z.val 2) 0 = z.val 1
    grind
  simp_all

theorem squareToTriangle_triangle0_zero z :
    (squareToTriangle (cubeTriangle0 z)).val 1 = 0 := by
  have hs := (Fin.sum_univ_three z.val).symm.trans z.property.2
  change max (z.val 2 - (1 - z.val 0)) 0 = 0
  grind [z.property.1 1]

theorem squareToTriangle_boundary z (hz : z ∈ Cube.boundary (Fin 2)) :
    ∃ i : Fin 3, (squareToTriangle z).val i = 0 := by
  cases' hz with i hi
  fin_cases i
  · rcases hi with hi | hi
    · refine ⟨2, ?_⟩
      change z 0 = 0 at hi
      change min (z 0 : ℝ) (z 1) = 0
      rw [hi]
      exact min_eq_left (z 1).property.1
    · refine ⟨0, ?_⟩
      change 1 - (z 0 : ℝ) = 0
      simp_all
  · rcases hi with hi | hi
    · refine ⟨2, ?_⟩
      change z 1 = 0 at hi
      change min (z 0 : ℝ) (z 1) = 0
      rw [hi]
      exact min_eq_right (z 0).property.1
    · refine ⟨1, ?_⟩
      change z 1 = 1 at hi
      change max ((z 0 : ℝ) - z 1) 0 = 0
      rw [hi]
      exact max_eq_right (sub_nonpos.mpr (z 0).property.2)
