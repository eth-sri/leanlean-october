/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

import RequestProject.TopologicalSingular.AffineSubdivisionNaturality
noncomputable section


/-! # The universal singular chains for barycentric subdivision -/

namespace FiniteChains.SingularSubdivision

open AffineVertexChains

def generator n : VertexChains.Chain (TopologicalSingular.Domain n) n :=
  Finsupp.single (standardVertices n) 1

def model n : TopologicalSingular.Chain (TopologicalSingular.Domain n) n :=
  realize (convex_stdSimplex ℝ _) n
    (VertexChains.subdivide (center (convex_stdSimplex ℝ _)) n (generator n))

def homotopyModel n : TopologicalSingular.Chain (TopologicalSingular.Domain n) (n + 1) :=
  realize (convex_stdSimplex ℝ _) _
    (VertexChains.subdivideHomotopy (center (convex_stdSimplex ℝ _)) n (generator n))

theorem boundary_model n :
    TopologicalSingular.boundary n (model (n + 1)) =
      ∑ i : Fin (n + 2), (-1) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) n (model n) := by
  rw [model, ← realize_boundary, ← VertexChains.subdivide_boundary, generator,
    VertexChains.boundary_single]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (by
    simpa [VertexChains.map_single, standardMap_vertices, VertexChains.face, model, generator]
      using (realize_standard_subdivide_naturality i.succAbove
        (Finsupp.single (standardVertices n) 1)).symm)

theorem homotopy_on_boundary n :
    realize (convex_stdSimplex ℝ (Fin (n + 2))) (n + 1)
        (VertexChains.subdivideHomotopy (center (convex_stdSimplex ℝ (Fin (n + 2)))) n
          (VertexChains.boundary n (generator (n + 1)))) =
      ∑ i : Fin (n + 2), (-1) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) (n + 1) (homotopyModel n) := by
  rw [generator, VertexChains.boundary_single]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (by
    simpa [VertexChains.map_single, standardMap_vertices, VertexChains.face, homotopyModel, generator]
      using (realize_standard_homotopy_naturality i.succAbove
        (Finsupp.single (standardVertices n) 1)).symm)

theorem homotopyModel_identity n :
    TopologicalSingular.boundary (n + 1) (homotopyModel (n + 1)) +
      (∑ i : Fin (n + 2), (-1) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) (n + 1) (homotopyModel n)) =
      model (n + 1) - Finsupp.single (ContinuousMap.id (TopologicalSingular.Domain (n + 1))) 1 := by
  have he := congrArg (realize (convex_stdSimplex ℝ (Fin (n + 2))) (n + 1))
    (VertexChains.subdivideHomotopy_identity_succ
      (center (convex_stdSimplex ℝ (Fin (n + 2)))) n (generator (n + 1)))
  grind [map_add, map_sub, realize_boundary, homotopy_on_boundary, homotopyModel, model, generator, realize_single, affineEval_standardVertices]
