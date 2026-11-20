module

public import RequestProject.TopologicalSingular.CoherentEdgeNormalization
public import RequestProject.TopologicalSingular.TriangleBasedNormalization

@[expose] public section

namespace FiniteChains.TopologicalSingular
open scoped unitInterval Topology
universe u
variable {X : Type u} [TopologicalSpace X] [SimplyConnectedSpace X]

variable (x : X) (tau : Simplex X 2)

theorem normalizedEdgeHomotopies_coherent
    (i j : Fin 3) (t : I) (z w : Domain 1)
    (h : stdSimplex.map (SimplexCategory.δ i) z = stdSimplex.map (SimplexCategory.δ j) w) :
    normalizedEdgeHomotopy x (face i tau) (t, z) = normalizedEdgeHomotopy x (face j tau) (t, w) := by
  by_cases hij : i = j
  · subst j
    solve_by_elim [simplex_face_injective]
  · obtain ⟨hz, hw⟩ := simplex_face_intersection_boundary i j hij z w h
    rw [normalizedEdgeHomotopy_boundary x _ _ _ hz, normalizedEdgeHomotopy_boundary x _ _ _ hw,
      face_apply, face_apply, h]

theorem normalizedTriangle_exists :
    ∃ g : Simplex X 2, ∃ F : tau.Homotopy g,
      ∀ (i : Fin 3) (t : I) (z : Domain 1),
        F (t, stdSimplex.map (SimplexCategory.δ i) z) = normalizedEdgeHomotopy x (face i tau) (t, z) :=
  simplex_face_homotopy_extension tau
    _
    (normalizedEdgeHomotopies_coherent x tau)
    (fun i z => (normalizedEdgeHomotopy x (face i tau)).apply_zero z)

noncomputable def normalizedTriangle :=
  (normalizedTriangle_exists x tau).choose

noncomputable def normalizedTriangleHomotopy :
    tau.Homotopy (normalizedTriangle x tau) :=
  (normalizedTriangle_exists x tau).choose_spec.choose

variable (i : Fin 3)

theorem normalizedTriangleHomotopy_face (t : I) (z : Domain 1) :
    normalizedTriangleHomotopy x tau (t, stdSimplex.map (SimplexCategory.δ i) z) =
      normalizedEdgeHomotopy x (face i tau) (t, z) :=
  (normalizedTriangle_exists x tau).choose_spec.choose_spec i t z

theorem normalizedTriangle_face :
    face i (normalizedTriangle x tau) = ContinuousMap.const (Domain 1) x := by
  apply ContinuousMap.ext
  intro z
  have he := normalizedTriangleHomotopy_face x tau i 1 z
  aesop

end FiniteChains.TopologicalSingular
