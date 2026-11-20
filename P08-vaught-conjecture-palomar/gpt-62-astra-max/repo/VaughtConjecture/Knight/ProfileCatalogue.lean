/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TerminalProfile

/-! # Canonical members and protected decoders for a family of scalar profiles -/

@[expose] public section
namespace VaughtConjecture.Knight.ProfileCatalogue
open Transform Value ExtOrd CanonicalPairedInverse TerminalProfile
noncomputable section
variable {Z X : Type*} [Fintype X]

/-- The scalar algorithms need only closure under a positive visible cap followed by normalization. -/
structure Family (Z X : Type*) [Fintype X] (j : ℕ) where
  profile : Z → X → ExtOrd
  admitted : Z → Prop
  realize : ∀ {s}, 1 ≤ j → admitted s → ∀ h, ∃ z, admitted z ∧ profile z = encoded (profile s) j h

variable {j B : ℕ} (F : Family Z X j) {s : Z} {a : X → ExtOrd}

abbrev Member : Type _ := {a : X → ExtOrd // a ∈ CanonicalPairedProfiles.inventory X j ∧ ∃ z, F.admitted z ∧ F.profile z = a}

noncomputable abbrev memberFintype : Fintype (Member F) :=
  ((CanonicalPairedProfiles.inventory_finite X j).subset (fun _ h => h.1)).fintype

theorem supported_decoder (hj : 1 ≤ j) (hs : F.admitted s) :
    ∃ Q, F.admitted Q ∧ F.profile Q ∈ CanonicalPairedProfiles.inventory X j ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧
        (∀ d, δ (F.profile Q d) = F.profile s d) ∧
        (∀ d, δ (F.profile Q d) = ⊥ → F.profile Q d = ⊥) ∧
        ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) (F.profile s) (δ x) := by
  obtain ⟨z,hz,he⟩ := F.realize hj hs 0
  refine ⟨z,hz,?_⟩; rw [he]
  obtain ⟨δ,hδ,hr,hsup⟩ := decoder (F.profile s) j 0
  refine ⟨canonical _ _ _,δ,hδ,hr,fun d hd => ?_,hsup⟩
  apply (PairedSlotEncoding.normalize_bot_iff j _ d).mpr
  exact min_eq_bot.mpr (Or.inl ((hr d).symm.trans hd))

structure Repair (a : X → ExtOrd) (s : Z) (B : ℕ) where
  encoded : Z
  admitted : F.admitted encoded
  canonical : F.profile encoded ∈ CanonicalPairedProfiles.inventory X j
  prefix_eq : CappedEq (F.profile encoded) a (grid j B)
  decoder : ExtOrd → ExtOrd
  witness : Witness (gTop j) decoder
  readback : ∀ d, decoder (F.profile encoded d) = F.profile s d
  grid_fixed : ∀ b < B, decoder (grid j b) = grid j b
  reaches : grid j B ≤ decoder (grid j B)
  boundary_fixed : ∀ d, a d < grid j B → decoder (a d) = a d

variable {F} in
theorem Repair.fixedBelow (r : Repair F a s B) {n : ℕ} {z : ExtOrd}
    (hz : z ∈ PairedSlotComparison.sourceGrid j n) (hlt : z < grid j B) : r.decoder z = z := by
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact r.witness.bot
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    apply r.grid_fixed
    by_contra hn
    have hi : B ≤ i := Nat.le_of_not_gt hn
    exact (not_le_of_gt hlt) (ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl))

def Repair.member (r : Repair F a s B) : Member F := ⟨_,r.canonical,_,r.admitted,rfl⟩

theorem exists_repair (hj : 1 ≤ j) (ha : a ∈ CanonicalPairedProfiles.inventory X j) (hs : F.admitted s)
    (hag : CappedEq a (F.profile s) (grid j B)) : Nonempty (Repair F a s B) := by
  let v := F.profile s
  let h := Ordinal.omega0 * B + j
  have hcut : grid j B < ofOrd (floor v h) := ofOrd_lt_ofOrd.mpr (above v h (Finset.mem_insert_self _ _))
  have hv : CappedEq a (capped v j h) (grid j B) := fun d => (hag d).trans ((cap_prefix v j h d).symm)
  obtain ⟨z,hz,he⟩ := F.realize hj hs h
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ := exists_supported_inverse ha (proper v j h) hv
  let δ := collapseBlock (floor v h) ∘ κ
  have hd (d) : δ (F.profile z d) = v d := by rw [he]; exact (congrArg _ (hread d)).trans (collapse v j h d)
  have hc := collapseBlock_witness j (limit v h)
  have hp : CappedEq (F.profile z) a (grid j B) := he ▸ CanonicalPairedProfiles.normalize_cap X j ha hv
  refine ⟨⟨z,hz,he ▸ canonical v j h,hp,δ,Witness.comp_of_bottom_reflecting hw hc le_rfl (collapseBlock_reflects_bottom _),hd,?_,?_,?_⟩⟩
  · intro b hb
    change collapseBlock _ (κ _) = _
    rw [hfix b hb]; apply collapseBlock_of_lt
    exact lt_of_le_of_lt (ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)) hcut
  · exact (collapseBlock_of_lt hcut).ge.trans (hc.mono hreach)
  · intro d hh
    exact (congrArg δ (PairedSlotEncoding.eq_of_cap_eq_lt (hp d).symm hh)).trans
      ((hd d).trans (PairedSlotEncoding.eq_of_cap_eq_lt (hag d) hh).symm)
end
end VaughtConjecture.Knight.ProfileCatalogue
