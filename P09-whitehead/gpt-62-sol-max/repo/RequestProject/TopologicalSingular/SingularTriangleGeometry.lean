module

/- Adapted from the local 2026-09-11 Lean audit; see PROVENANCE.json. -/

public import RequestProject.TopologicalSingular.SingularChainH0
public import RequestProject.TopologicalSingular.SimplexCoordinates

@[expose] public section

/-! # Explicit triangle coordinates for singular path relations -/


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FiniteChains.TopologicalSingular

open Set Topology

noncomputable def coordinate (n : ℕ) (i : Fin (n + 1)) : C(Domain n, unitInterval) :=
  ⟨fun z => ⟨z.val i, mem_Icc_of_mem_stdSimplex z.property i⟩,
    ((continuous_apply i).comp continuous_subtype_val).subtype_mk _⟩

theorem triangle_face_zero (z : Domain 1) :
    (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z).val = ![0, z.val 0, z.val 1] := by
  erw [simplex_map_succAbove (0 : Fin 3) z]
  funext j
  fin_cases j <;> rfl

theorem triangle_face_one (z : Domain 1) :
    (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z).val = ![z.val 0, 0, z.val 1] := by
  erw [simplex_map_succAbove (1 : Fin 3) z]
  funext j
  fin_cases j <;> rfl

theorem triangle_face_two (z : Domain 1) :
    (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z).val = ![z.val 0, z.val 1, 0] := by
  erw [simplex_map_succAbove (2 : Fin 3) z]
  funext j
  fin_cases j <;> rfl

noncomputable def squareTriangle0 : C(Domain 2, unitInterval × unitInterval) :=
  ⟨fun z => (coordinate 2 2 z, unitInterval.symm (coordinate 2 0 z)),
    (coordinate 2 2).continuous.prodMk (unitInterval.continuous_symm.comp (coordinate 2 0).continuous)⟩

noncomputable def squareTriangle1 : C(Domain 2, unitInterval × unitInterval) :=
  (⟨Prod.swap, continuous_swap⟩ : C(_, _)).comp squareTriangle0

theorem squareTriangle0_faces (z : Domain 1) :
    squareTriangle0 (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, 1) ∧
    squareTriangle0 (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, stdSimplexHomeomorphUnitInterval z) ∧
    squareTriangle0 (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z) =
        (0, stdSimplexHomeomorphUnitInterval z) := by
  have hz := z.property.2
  rw [Fin.sum_univ_two] at hz
  refine ⟨?_, ?_, ?_⟩ <;>
    (apply Prod.ext <;> apply Subtype.ext <;>
      change _ = _ <;>
      simp only [squareTriangle0, ContinuousMap.coe_mk, coordinate, unitInterval.coe_symm_eq,
        triangle_face_zero, triangle_face_one, triangle_face_two,
        stdSimplexHomeomorphUnitInterval] <;>
      (dsimp [Matrix.vecHead, Matrix.vecTail]; all_goals linarith))

theorem squareTriangle1_faces (z : Domain 1) :
    squareTriangle1 (stdSimplex.map (SimplexCategory.δ (0 : Fin 3)) z) =
        (1, stdSimplexHomeomorphUnitInterval z) ∧
    squareTriangle1 (stdSimplex.map (SimplexCategory.δ (1 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, stdSimplexHomeomorphUnitInterval z) ∧
    squareTriangle1 (stdSimplex.map (SimplexCategory.δ (2 : Fin 3)) z) =
        (stdSimplexHomeomorphUnitInterval z, 0) := by
  obtain ⟨h₀, h₁, h₂⟩ := squareTriangle0_faces z
  simp [squareTriangle1, h₀, h₁, h₂]

end FiniteChains.TopologicalSingular
