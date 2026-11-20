/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TerminalBlock
public import VaughtConjecture.Knight.CanonicalPairedInverse

/-! # A fresh proper representative of a finite profile, including literal top -/

@[expose] public section
namespace VaughtConjecture.Knight.TerminalProfile
open Transform Value ExtOrd PairedSlotEncoding
noncomputable section
variable {X : Type*} [Fintype X] (p : X → ExtOrd) (j : ℕ) (h : Ordinal.{0})

def floor := Ordinal.omega0 * ((insert h (values p)).sup id + 1)

theorem limit : limitPart (floor p h) = floor p h := limitPart_omega0_mul _

theorem above {a : Ordinal.{0}} (ha : a ∈ insert h (values p)) : a < floor p h :=
  (Order.lt_add_one_iff.mpr (Finset.le_sup (f := id) ha)).trans_le
    (Ordinal.le_mul_right _ Ordinal.omega0_pos)

theorem cases (d) : p d < ofOrd (floor p h) ∨ p d = ⊤ := by
  rcases ExtOrd.cases (p d) with hz | ht | ⟨a, ha⟩
  · exact Or.inl (hz ▸ bot_lt_iff_ne_bot.mpr (ofOrd_ne_bot _))
  · exact Or.inr ht
  · rw [ha]; exact Or.inl (ofOrd_lt_ofOrd.mpr (above p h (Finset.mem_insert_of_mem (mem_values.mpr ⟨d,ha⟩))))

def bound := ofOrd (floor p h + j)

theorem visible : SelfVis j (bound p j h) := by
  apply selfVis_ofOrd_iff.mpr
  simpa only [limit] using (finitePart_limitPart_add_nat (floor p h) j).ge

theorem le_bound : ofOrd (floor p h) ≤ bound p j h := ofOrd_le_ofOrd.mpr le_self_add

abbrev capped (d) := min (p d) (bound p j h)

abbrev encoded := normalize j (capped p j h)

theorem proper (d) : capped p j h d ≠ ⊤ := fun he => ofOrd_ne_top _ (min_eq_top.mp he).2

theorem cap_prefix : CappedEq (capped p j h) p (ofOrd h) := fun d => by
  rw [capped, min_assoc, min_eq_right ((ofOrd_le_ofOrd.mpr (above p h (Finset.mem_insert_self _ _)).le).trans (le_bound p j h))]

theorem canonical : encoded p j h ∈ CanonicalPairedProfiles.inventory X j :=
  CanonicalPairedProfiles.normalize_mem_inventory _ _ (proper p j h)

theorem collapse (d) : collapseBlock (floor p h) (capped p j h d) = p d :=
  collapseBlock_min (le_bound p j h) (cases p h d)

/-- One decoder recovers every field and is supported on the original profile at every argument. -/
theorem decoder : ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧
    (∀ d, δ (encoded p j h d) = p d) ∧
    ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) p (δ x) := by
  let β := bound p j h
  have hβ := visible p j h
  have hG : ∀ z ∈ ({β} : Finset ExtOrd), SelfVis j z := by simpa using hβ
  refine ⟨collapseBlock (floor p h) ∘ PairedSlotDecoder.decode j (values (capped p j h)) {β} β,
    Witness.comp_of_bottom_reflecting (PairedSlotDecoder.decode_witness hG hβ)
      (collapseBlock_witness j (limit p h)) le_rfl (collapseBlock_reflects_bottom _), ?_, ?_⟩
  · intro d
    rw [Function.comp_apply, encoded, PairedSlotDecoder.decode_normalize hG hβ (proper p j h)]; exact collapse p j h d
  · intro x
    rw [Function.comp_apply]
    rcases PairedSlotDecoder.decode_supported (j := j) (K := j) (p := capped p j h) le_rfl (Finset.mem_singleton_self β) x with hz | hb | ⟨d,i,hi,he⟩
    · rw [hz]; exact Or.inl (collapseBlock_witness j (limit p h)).bot
    · rw [Finset.mem_singleton.mp (Finset.mem_coe.mp hb), collapseBlock_of_le (le_bound p j h)]
      exact Or.inr (Or.inl rfl)
    · rw [he, capped]
      rcases cases p h d with hl | ht
      · rw [min_eq_left (hl.le.trans (le_bound p j h)), collapseBlock_of_lt (evr_lt_of_lt_limit (limit p h) hl j i)]
        exact Or.inr (Or.inr ⟨d,i,hi,rfl⟩)
      · rw [ht, min_top_left, evr_eq_self_of_selfVis hβ i, collapseBlock_of_le (le_bound p j h)]
        exact Or.inr (Or.inl rfl)
end
end VaughtConjecture.Knight.TerminalProfile
