import RequestProject.SurfaceFullCubeFilling


/-! The actual link poset of the restored positive corner. -/
namespace FiniteChains.Davis
open RACG Mirror Comb
universe u
variable {V : Type u} [DecidableEq V] (A : CommRel V)

theorem positiveCorner_le_iff c :
    positiveCorner A ≤ c ↔ c.sgn = 0 := by
  constructor
  · intro h
    funext v
    by_cases hv : v ∈ c.spx
    · exact c.sgn_eq_zero v hv
    · exact (h.2 v hv).symm
  · intro h
    exact ⟨Finset.empty_subset _, by aesop⟩

theorem le_positiveCorner_iff c :
    c ≤ positiveCorner A ↔ c = positiveCorner A := by
  constructor
  · intro h
    apply QCube.ext'
    · exact Finset.Subset.antisymm h.1 (Finset.empty_subset _)
    · exact h.2
  simp_all

theorem positiveCorner_lt_iff c :
    positiveCorner A < c ↔ c.spx.Nonempty ∧ c.sgn = 0 := by
  rw [lt_iff_le_and_ne, positiveCorner_le_iff]
  constructor
  · rintro ⟨hs, hn⟩
    refine ⟨Finset.nonempty_iff_ne_empty.mpr ?_, hs⟩
    intro he
    apply hn
    symm
    apply QCube.ext' he
    tauto
  · rintro ⟨hne, hs⟩
    refine ⟨hs, ?_⟩
    intro he
    have hz := congrArg QCube.spx he
    exact (Finset.nonempty_iff_ne_empty.mp hne) hz.symm

/-- The strict upper interval of the actual restored corner is precisely the surface
simplex poset, with its actual face order. -/
def positiveCornerLinkEquiv : Set.Ioi (positiveCorner A) ≃o NeSpx A where
  toFun c := ⟨c.1.spx, (positiveCorner_lt_iff A c.1).mp c.2 |>.1, c.1.isSimplex⟩
  invFun σ := ⟨surfaceFullCube A σ, (positiveCorner_lt_iff A _).mpr ⟨σ.2.1, rfl⟩⟩
  left_inv c := by
    apply Subtype.ext
    apply QCube.ext' (by rfl)
    intro v _
    exact (congrFun ((positiveCorner_lt_iff A c.1).mp c.2).2 v).symm
  right_inv σ := rfl
  map_rel_iff' := by
    intro c d
    constructor
    · intro h
      refine ⟨h, ?_⟩
      simp [((positiveCorner_lt_iff A c.1).mp c.2).2, ((positiveCorner_lt_iff A d.1).mp d.2).2]
    · exact fun h => h.1
