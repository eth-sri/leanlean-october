import Mathlib.Tactic

import RequestProject.GenusSpineCoordinateSupport

/-! The actual surviving spine is closed under the retained-cube retraction. -/
namespace FiniteChains.Davis.Genus

variable (q : ℕ) [NeZero q]

theorem genus_positive_old_cell_survives (c : QOld (cmpRel (GenusVertex q)))
    (hsgn : c.1.sgn = 0) (hdim : c.1.spx.card ≤ 2) :
    (Sum.inl c : GenusTruncatedCell q) ∈ genusSpineCellSet q := by
  refine ⟨hdim, ?_⟩
  intro hremoved
  obtain ⟨⟨t, f⟩, hp, he⟩ := List.mem_map.mp hremoved
  dsimp! at *
  subst f
  have hi := (genusChainCollapse_isPairCollapse q).pair_inc hp
  by_cases htwo : c.1.spx.card = 2
  · simp [spineInc, htwo] at hi
    rw [qCubeToCoordinate_sgn_zero c.1 hsgn] at hi
    obtain ⟨j, _, _, ht⟩ := mem_cofaces.mp hi
    have hpos : t = posCube (freeSet t) := by
      rw [ht, update_posCube, freeSet_posCube]
    exact genusChainCollapse_old_face_nonpositive q t (qCubeToCoordinate c.1) hp hpos
  · simp [spineInc, htwo] at hi

variable (c : GenusSpineCell q)
theorem genusSpine_retraction_survives  :
    oldCellIncl (truncatedCellRetraction c.1) ∈ genusSpineCellSet q := by
  cases hc : c.1 with
  | inl a => simpa [oldCellIncl, truncatedCellRetraction, hc] using c.2
  | inr σ =>
      have hs := c.2
      rw [hc] at hs
      have hcard := genusSpine_cut_card_le_two q σ hs
      apply genus_positive_old_cell_survives q (posQCube ⟨σ.1, σ.2⟩) rfl hcard

/-- The retained-cube retraction is an actual endomorphism of the surviving spine. -/
def genusSpineRetraction  : GenusSpineCell q :=
  ⟨oldCellIncl (truncatedCellRetraction c.1), genusSpine_retraction_survives q c⟩

theorem genusSpineRetraction_monotone : Monotone (genusSpineRetraction q) :=
  fun _ _ h => oldCellIncl_monotone (truncatedCellRetraction_monotone h)

abbrev genusSpine_le_retraction   :=
  truncatedCell_le_retraction c.1

end FiniteChains.Davis.Genus
