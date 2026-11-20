module

public import RequestProject.TopologicalSingular.SimplexHornFiller
public import RequestProject.TopologicalSingular.StickTriangleComparison

@[expose] public section

namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] {n : ℕ}

/-- Fill a horn using the actual singular-simplex and face operators of this
project. Agreement is required only where the prescribed faces intersect. -/
theorem singular_horn_filler_exists (i : Fin _)
    (g : ∀ j : Fin _, j ≠ i → Simplex X n)
    (hg : ∀ (j k : Fin _) (hj : j ≠ i) (hk : k ≠ i)
      (z w : Domain n),
      stdSimplex.map (SimplexCategory.δ j) z = stdSimplex.map (SimplexCategory.δ k) w →
      g j hj z = g k hk w) :
    ∃ tau : Simplex X _, ∀ (j : Fin _) (hj : j ≠ i), face j tau = g j hj := by
  let faces :=
    fun k => g _ (Fin.succAbove_ne i k)
  have hfaces : SimplexHornFaceCompatible i faces := by
    intro j k z w h
    apply hg _ _
    simp_all [simplex_face_eq_faceMap]
  let tau := simplexHornFiller i faces hfaces
  refine ⟨tau, ?_⟩
  intro j hj
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
  apply ContinuousMap.ext
  intro z
  change tau (stdSimplex.map (SimplexCategory.δ (i.succAbove k)) z) = faces k z
  grind [simplex_face_eq_faceMap, simplexHornFiller_face]

end FiniteChains.TopologicalSingular
