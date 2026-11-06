module

public import Mathlib.Tactic

@[expose] public section

namespace HordijkSteelThreshold

/-- Deterministic nested sets realizing every possible finite pool size. -/
noncomputable def finiteInitialSegment (X : Type*) [Fintype X] (k : ℕ) : Finset X :=
  (Finset.univ.filter (fun i : Fin (Fintype.card X) => i.val < k)).map
    (Fintype.equivFin X).symm.toEmbedding

theorem finiteInitialSegment_mono (X : Type*) [Fintype X] :
    Monotone (finiteInitialSegment X) :=
  fun _ _ hab => Finset.map_subset_map.mpr fun _ hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans_le hab⟩

theorem card_finiteInitialSegment (X : Type*) [Fintype X]
    (k : ℕ) (hk : k ≤ Fintype.card X) :
    (finiteInitialSegment X k).card = k := by
  rw [finiteInitialSegment, Finset.card_map, Fin.card_filter_val_lt, min_eq_right hk]

end HordijkSteelThreshold
