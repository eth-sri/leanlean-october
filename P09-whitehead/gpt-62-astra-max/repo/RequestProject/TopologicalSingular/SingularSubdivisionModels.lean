module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.AffineSubdivisionNaturality

@[expose] public section

/-! # The universal singular chains for barycentric subdivision -/

noncomputable section

namespace FiniteChains.SingularSubdivision

open AffineVertexChains

variable (n : ℕ)

def generator : VertexChains.Chain (TopologicalSingular.Domain n) n :=
  Finsupp.single (standardVertices n) 1

def model :=
  realize (convex_stdSimplex ℝ (Fin (n + 1))) n
    (VertexChains.subdivide (center (convex_stdSimplex ℝ (Fin (n + 1)))) n (generator n))

def homotopyModel :=
  realize (convex_stdSimplex ℝ (Fin (n + 1))) _
    (VertexChains.subdivideHomotopy (center (convex_stdSimplex ℝ (Fin (n + 1)))) n (generator n))

theorem boundary_model :
    TopologicalSingular.boundary n (model _) =
      ∑ i : Fin _, (-1) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) n (model n) := by
  rw [model, ← realize_boundary, ← VertexChains.subdivide_boundary, generator,
    VertexChains.boundary_single]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (by
    simpa only [VertexChains.map_single, standardMap_vertices, VertexChains.face, model, generator]
      using (realize_standard_subdivide_naturality i.succAbove
        (Finsupp.single (standardVertices n) 1)).symm)

theorem homotopy_on_boundary :
    realize (convex_stdSimplex ℝ (Fin (n + 2))) _
        (VertexChains.subdivideHomotopy (center (convex_stdSimplex ℝ (Fin (n + 2)))) n
          (VertexChains.boundary n (generator (n + 1)))) =
      ∑ i : Fin _, (-1) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) _ (homotopyModel n) := by
  rw [generator, VertexChains.boundary_single]
  simp only [map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (by
    simpa only [VertexChains.map_single, standardMap_vertices, VertexChains.face, homotopyModel, generator]
      using (realize_standard_homotopy_naturality i.succAbove
        (Finsupp.single (standardVertices n) 1)).symm)

theorem homotopyModel_identity :
    TopologicalSingular.boundary _ (homotopyModel _) +
      (∑ i : Fin _, (-1) ^ i.val •
        TopologicalSingular.map (standardMap i.succAbove) _ (homotopyModel n)) =
      model _ - Finsupp.single (ContinuousMap.id _) 1 := by
  have he := congrArg (realize (convex_stdSimplex ℝ (Fin (n + 2))) (n + 1))
    (VertexChains.subdivideHomotopy_identity_succ
      (center (convex_stdSimplex ℝ (Fin (n + 2)))) n (generator (n + 1)))
  rw [map_add, map_sub, realize_boundary, homotopy_on_boundary] at he
  simpa only [homotopyModel, model, generator, realize_single, affineEval_standardVertices] using he

end FiniteChains.SingularSubdivision
