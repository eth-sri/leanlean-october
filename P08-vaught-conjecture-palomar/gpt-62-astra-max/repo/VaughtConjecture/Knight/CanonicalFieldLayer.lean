/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ProfileCatalogue
public import VaughtConjecture.Knight.PairedCoupledSections

/-! # Canonical controllers normalized over the complete field inventory

`X` retains all fields, including fields not yet present at this grade. Both
normalization and controller agreement cuts use all of `X`. Only the actual
occurrence map is projected when checking inherited-row lawfulness. The new
controller family and its selected sections are constructed, not supplied.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalFieldLayer
open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition
open PairedSlotEncoding PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X] (occ : Cell D → X)

def Profile := {p : X → ExtOrd // RespectsSemantics sem (p ∘ occ) ∧
  p ∈ CanonicalPairedProfiles.inventory X j}

instance : Fintype (Profile sem j X occ) :=
  ((CanonicalPairedProfiles.inventory_finite X j).subset (fun _ h => h.2)).fintype

theorem profile_short (q : Profile sem j X occ) (x : X) : Short j (q.val x) :=
  CanonicalPairedProfiles.inventory_short X j q.property.2 x

def ceiling : ExtOrd := ofOrd (Ordinal.omega0 * (2 * Fintype.card X + 1 : ℕ) + j)

theorem grid_bound {h : ExtOrd} (hh : h ∈ sourceGrid j (Fintype.card X)) :
    h ≤ ceiling j X := by
  classical
  rcases Finset.mem_insert.mp hh with rfl | hh
  · exact bot_le
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
    have hb' : b ≤ 2 * Fintype.card X + 1 := by
      have := Finset.mem_range.mp hb
      omega
    exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)

theorem profile_bound (q : Profile sem j X occ) (x : X) : q.val x ≤ ceiling j X := by
  apply (CanonicalPairedProfiles.inventory_bound X j q.property.2 x).trans
  exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl)

theorem grid_short {h : ExtOrd} (hh : h ∈ sourceGrid j (Fintype.card X)) :
    Short j h := by
  classical
  rcases Finset.mem_insert.mp hh with rfl | hh
  · exact Or.inl rfl
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hh
    exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)

variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : ∀ d : Cell D, D.scope d ≠ A)
variable (hg : ∀ d : Cell D, D.grade d ≤ j)

def encode {p : X → ExtOrd} (hp : RespectsSemantics sem (p ∘ occ))
    (ht : ∀ x, p x ≠ ⊤) : Profile sem j X occ := by
  refine ⟨PairedSlotEncoding.normalize j p, ?_,
    CanonicalPairedProfiles.normalize_mem_inventory X j ht⟩
  have hr := FiniteOrbitEmbedding.map_respects (hp.toBelow (A, j))
    (fun d => hg d.1) (PairedSlotIncoming.encoder_witness j (values p))
    (PairedSlotIncoming.encoder_reflects_bottom j (values p))
  have hw := hr.toRespects
    (fun d => ⟨D.isPlan.subset_of_mem (D.scope_mem_plan d), hg d⟩)
  simpa only [Function.comp_def, PairedSlotIncoming.encoder_profile] using hw

/-- Full field profiles lawful on the current occurrences form a repairable catalogue. -/
def family : ProfileCatalogue.Family (X → ExtOrd) X j where
  profile := id
  admitted p := RespectsSemantics sem (p ∘ occ)
  realize := by
    intro s _ hs h
    have hcap := ((hs.toBelow (A,j)).cap (TerminalProfile.visible s j h)).toRespects
      (fun d => ⟨D.scope_subset d, hg d⟩)
    let b := encode sem j X occ hg (p := TerminalProfile.capped s j h) hcap (TerminalProfile.proper s j h)
    exact ⟨b.val,b.property.1,rfl⟩

variable {p : X → ExtOrd} (hp : RespectsSemantics sem (p ∘ occ)) (ht : ∀ x, p x ≠ ⊤)
variable {G : Finset ExtOrd} {C : ExtOrd}

end
end VaughtConjecture.Knight.CanonicalFieldLayer
