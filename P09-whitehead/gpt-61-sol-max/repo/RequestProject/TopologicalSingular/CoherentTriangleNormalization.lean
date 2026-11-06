import Mathlib.Tactic

import RequestProject.TopologicalSingular.CoherentEdgeNormalization
import RequestProject.TopologicalSingular.TriangleBasedNormalization

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

  (x : X)
  (tau : Simplex X 2)
theorem normalizedEdgeHomotopies_coherent  
    (i j : Fin 3) (t : I) (z w : Domain 1)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    normalizedEdgeHomotopy x (face i tau) (t, z) = normalizedEdgeHomotopy x (face j tau) (t, w) := by
  by_cases hij : i = j
  · subst j
    rw [simplex_face_injective i h]
  · obtain ⟨hz, hw⟩ := simplex_face_intersection_boundary i j hij z w h
    rw [normalizedEdgeHomotopy_boundary x _ _ _ hz, normalizedEdgeHomotopy_boundary x _ _ _ hw,
      face_apply, face_apply, h]

abbrev normalizedTriangle_exists    :=
  simplex_face_homotopy_extension tau
    (fun i => (normalizedEdgeHomotopy x (face i tau)).toContinuousMap)
    (normalizedEdgeHomotopies_coherent x tau)
    (fun i z => (normalizedEdgeHomotopy x (face i tau)).apply_zero z)

noncomputable def normalizedTriangle    :=
  (normalizedTriangle_exists x tau).choose

noncomputable def normalizedTriangleHomotopy    :=
  (normalizedTriangle_exists x tau).choose_spec.choose

theorem normalizedTriangleHomotopy_face  
    (i : Fin 3) (t : I) (z : Domain 1) :
    normalizedTriangleHomotopy x tau (t, stdSimplex.map (SimplexCategory.δ i) z) =
      normalizedEdgeHomotopy x (face i tau) (t, z) :=
  (normalizedTriangle_exists x tau).choose_spec.choose_spec i t z

theorem normalizedTriangle_face   (i : Fin 3) :
    face i (normalizedTriangle x tau) = ContinuousMap.const (Domain 1) x := by
  apply ContinuousMap.ext
  intro z
  have he := normalizedTriangleHomotopy_face x tau i 1 z
  rw [(normalizedTriangleHomotopy x tau).apply_one, (normalizedEdgeHomotopy x (face i tau)).apply_one] at he
  exact he

end FiniteChains.TopologicalSingular
