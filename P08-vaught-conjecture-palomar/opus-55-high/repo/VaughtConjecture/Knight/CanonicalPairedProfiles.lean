/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairedPrefix

/-! # Canonical inventories on the complete field vector

This is a separate inventory, not a change to the refuted all-short family.
The finite type `X` counts every field normalized together, including auxiliary
fields. No boundary-cardinality estimate is substituted for its cardinality.

The inventory supplies canonical representatives and relative capped agreement.
It does not yet supply a prefix-fixing inverse or coupled semantic sections.
The ordinary exact decoder below is deliberately not claimed to fix unused grids.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalPairedProfiles
open Transform Value ExtOrd PairedSlotEncoding PairedSlotProfiles SharpWitnessComposition
noncomputable section

section Inventory
variable (X : Type*) [Fintype X] (j : ℕ)

/-- Proper canonical fixed points on the complete inventory. -/
def inventory : Set (X → ExtOrd) :=
  {p | PairedSlotEncoding.normalize j p = p ∧ ∀ d, p d ≠ ⊤}

theorem inventory_coded {p} (hp : p ∈ inventory X j) d :
    p d ∈ ExtOrd.codedAlphabet (2 * Fintype.card X) j := by
  rw [← congrFun hp.1 d]
  exact normalize_mem j p d (hp.2 d)

theorem inventory_finite : (inventory X j).Finite :=
  (ExtOrd.codedLabellings_finite X (2 * Fintype.card X) j).subset
    (fun _ hp => inventory_coded X j hp)

section
variable {p : X → ExtOrd}

theorem inventory_short (hp : p ∈ inventory X j) d :
    Short j (p d) := by
  rw [← congrFun hp.1 d]
  exact normalize_short j p d

theorem inventory_bound (hp : p ∈ inventory X j) d :
    p d ≤ sourceCeiling j X := by
  rw [← congrFun hp.1 d]
  exact normalize_le_ceiling hp.2 d

theorem normalize_mem_inventory (hp : ∀ d, p d ≠ ⊤) :
    PairedSlotEncoding.normalize j p ∈ inventory X j := by
  refine ⟨CanonicalPairedEncoding.normalize_idempotent j p, ?_⟩
  intro d
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simpa only [PairedSlotEncoding.normalize, hb] using
      (show (⊥ : ExtOrd) ≠ ⊤ from hb ▸ hp d)
  · exact (hp d ht).elim
  · rw [normalize_ofOrd ha]
    exact ofOrd_ne_top _

end

/-- The relative prefix theorem applies coordinatewise to the full field vector,
including auxiliary fields, and uses the original grid cut. -/
theorem normalize_cap {a p} {B : ℕ}
    (ha : a ∈ inventory X j)
    (hag : ∀ d, min (a d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (p d) (ofOrd (Ordinal.omega0 * B + j))) d :
    min (PairedSlotEncoding.normalize j p d) (ofOrd (Ordinal.omega0 * B + j)) =
      min (a d) (ofOrd (Ordinal.omega0 * B + j)) :=
  CanonicalPairedPrefix.normalize_cap ha.1 ha.2 hag d

end Inventory

end
end VaughtConjecture.Knight.CanonicalPairedProfiles
