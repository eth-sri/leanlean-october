module

public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold

variable (X : Type*) [Fintype X]

    (k : ℕ)

/-- Deterministic nested sets realizing every possible finite pool size. -/
noncomputable def finiteInitialSegment   : Finset X :=
  (Finset.univ.filter (fun i : Fin (Fintype.card X) => i.val < k)).map
    (Fintype.equivFin X).symm.toEmbedding

theorem finiteInitialSegment_mono  :
    Monotone (finiteInitialSegment X) := by
  intro a b hab
  apply Finset.map_subset_map.mpr
  grind

theorem card_finiteInitialSegment
     (hk : k ≤ Fintype.card X) :
    (finiteInitialSegment X k).card = k := by
  rw [finiteInitialSegment, Finset.card_map, Fin.card_filter_val_lt, min_eq_right hk]

end HordijkSteelThreshold
