import Mathlib.Tactic

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.AffineSubdivisionNaturality

/-! # The universal singular chains for barycentric subdivision -/

namespace FiniteChains.SingularSubdivision

open AffineVertexChains

variable (n : ℕ)
noncomputable def generator  : VertexChains.Chain (TopologicalSingular.Domain n) n :=
  Finsupp.single (standardVertices n) 1

noncomputable def model   :=
  realize (convex_stdSimplex ℝ (Fin (n + 1))) n
    (VertexChains.subdivide (center (convex_stdSimplex ℝ (Fin (n + 1)))) n (generator n))

noncomputable def homotopyModel   :=
  realize (convex_stdSimplex ℝ (Fin (n + 1))) (n + 1)
    (VertexChains.subdivideHomotopy (center (convex_stdSimplex ℝ (Fin (n + 1)))) n (generator n))

theorem boundary_model  :
    TopologicalSingular.boundary n (model (n + 1)) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) n (model n) := by
  rw [model, ← realize_boundary, ← VertexChains.subdivide_boundary, generator,
    VertexChains.boundary_single]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (by
    simp_all [standardMap_vertices, VertexChains.face, model, generator, realize_standard_subdivide_naturality])

theorem homotopy_on_boundary  :
    realize (convex_stdSimplex ℝ (Fin (n + 2))) (n + 1)
        (VertexChains.subdivideHomotopy (center (convex_stdSimplex ℝ (Fin (n + 2)))) n
          (VertexChains.boundary n (generator (n + 1)))) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) (n + 1) (homotopyModel n) := by
  rw [generator, VertexChains.boundary_single]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (by
    simp_all [standardMap_vertices, VertexChains.face, homotopyModel, generator, realize_standard_homotopy_naturality])

theorem homotopyModel_identity  :
    TopologicalSingular.boundary (n + 1) (homotopyModel (n + 1)) +
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) (n + 1) (homotopyModel n)) =
      model (n + 1) - Finsupp.single (ContinuousMap.id (TopologicalSingular.Domain (n + 1))) 1 := by
  have he := congrArg (realize (convex_stdSimplex ℝ (Fin (n + 2))) (n + 1))
    (VertexChains.subdivideHomotopy_identity_succ
      (center (convex_stdSimplex ℝ (Fin (n + 2)))) n (generator (n + 1)))
  rw [map_add, map_sub, realize_boundary, homotopy_on_boundary] at he
  simpa only [homotopyModel, model, generator, realize_single, affineEval_standardVertices] using he

end FiniteChains.SingularSubdivision
