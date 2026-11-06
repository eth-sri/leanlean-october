/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PairedSlotIncoming

/-! # Finite lawful paired-slot profiles

On a fixed finite lower domain, every lawful labelling without literal top has
a lawful sharp representative in a fixed finite family. The representative
has a constructed incoming encoder and an exact outgoing decoder. The family
does not assume a lawful completion of any face, common-cut compatibility of
decoders, or a new-controller consistency theorem.

Literal top is supported by incoming normalization, but is excluded here because
the family's finite coded alphabet contains only bottom and proper ordinals.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.PairedSlotProfiles
open Transform Value ExtOrd PairedSlotEncoding SharpWitnessComposition
noncomputable section

section Profile
variable {X : Type*} [Fintype X]

theorem normalize_short (j : ℕ) (p : X → ExtOrd) (d : X) :
    Short j (PairedSlotEncoding.normalize j p d) := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · exact Or.inl (by simp [PairedSlotEncoding.normalize, hb])
  · exact Or.inr (Or.inl (by simp [PairedSlotEncoding.normalize, ht]))
  · rw [normalize_ofOrd ha]
    exact Or.inr (Or.inr ⟨_, rfl, by
      rw [finitePart_mul_add]
      exact offset_le j (values p) a⟩)

/-- A single visible proper source ceiling bounds every finite normalized profile
on the same carrier, regardless of the ordinal size of its original labels. -/
def sourceCeiling (j : ℕ) (X : Type*) [Fintype X] : ExtOrd :=
  ofOrd (Ordinal.omega0 * (2 * Fintype.card X : ℕ) + j)

theorem normalize_le_ceiling {j : ℕ} {p : X → ExtOrd}
    (hp : ∀ d, p d ≠ ⊤) (d : X) :
    PairedSlotEncoding.normalize j p d ≤ sourceCeiling j X := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · simp [PairedSlotEncoding.normalize, hb, bot_le]
  · exact (hp d ht).elim
  · have hr := rank_lt_card (j := j) (mem_values.mpr ⟨d, ha⟩)
    have hn := values_card_le p
    have hblock : block j (values p) a ≤ 2 * Fintype.card X := by
      unfold block
      split_ifs <;> omega
    rw [normalize_ofOrd ha]
    apply ofOrd_le_ofOrd.mpr
    apply add_le_add
    · gcongr
    · exact Nat.cast_le.mpr (offset_le j (values p) a)


