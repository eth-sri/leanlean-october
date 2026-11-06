import RequestProject.TopologicalSingular.SimplexHornFiller
import RequestProject.TopologicalSingular.StickTriangleComparison


namespace FiniteChains.TopologicalSingular
variable {X : Type} [TopologicalSpace X] {n : ℕ}

/-- Fill a horn using the actual singular-simplex and face operators of this
project. Agreement is required only where the prescribed faces intersect. -/
theorem singular_horn_filler_exists i
    (g : ∀ j, j ≠ i → Simplex X n)
    (hg : ∀ j k hj hk
      (z w : Domain n),
      stdSimplex.map (SimplexCategory.δ j) z = stdSimplex.map (SimplexCategory.δ k) w →
      g j hj z = g k hk w) :
    ∃ tau, ∀ j hj, face j tau = g j hj := by
  let faces :=
    fun k => g _ (i.succAbove_ne k)
  have hfaces : SimplexHornFaceCompatible i faces := by
    intro j k z w h
    grind [simplex_face_eq_faceMap]
  let tau := simplexHornFiller i faces hfaces
  refine ⟨tau, ?_⟩
  intro j hj
  obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq hj
  apply ContinuousMap.ext
  intro z
  change tau (stdSimplex.map (SimplexCategory.δ (i.succAbove k)) z) = faces k z
  rw [simplex_face_eq_faceMap]
  exact simplexHornFiller_face i faces hfaces k z
