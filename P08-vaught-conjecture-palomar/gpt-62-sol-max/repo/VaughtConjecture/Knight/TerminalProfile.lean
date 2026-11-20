/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalPairedInverse
public import VaughtConjecture.Knight.OrbitPrefixSupport
public import VaughtConjecture.Knight.ReceivingCatalogueRanks

@[expose] public section

namespace VaughtConjecture.Knight.TerminalProfile

open Transform Value ExtOrd PairedSlotEncoding PairedSlotComparison CanonicalPairedInverse CappedDonor.Ref

noncomputable section

variable {X : Type*} [Fintype X] (p : X → ExtOrd) (h : Ordinal.{0}) (j : ℕ)

def floor : Ordinal.{0} := Ordinal.omega0 * ((insert h (values p)).sup id + 1)

theorem floor_limit : limitPart (floor p h) = floor p h := limitPart_omega0_mul _

theorem lt_floor {a : Ordinal.{0}} (ha : a ∈ insert h (values p)) : a < floor p h :=
  (Order.lt_add_one_iff.mpr (Finset.le_sup (f := id) ha)).trans_le
    (Ordinal.le_mul_right _ Ordinal.omega0_pos)

theorem value_lt_floor (d : X) : p d < ofOrd (floor p h) ∨ p d = ⊤ := by
  rcases ExtOrd.cases (p d) with hb | ht | ⟨a, ha⟩
  · aesop
  · exact Or.inr ht
  · exact Or.inl (ha ▸ ofOrd_lt_ofOrd.mpr (lt_floor p h
      (Finset.mem_insert_of_mem (mem_values.mpr ⟨d, ha⟩))))

abbrev cap : ExtOrd := ofOrd (floor p h + j)

abbrev clipped (d : X) := min (p d) (cap p h j)

theorem floor_le_cap : ofOrd (floor p h) ≤ cap p h j := ofOrd_le_ofOrd.mpr le_self_add

theorem cutoff_lt_floor : ofOrd h < ofOrd (floor p h) :=
  (by simp_all [lt_floor])

theorem cap_visible : SelfVis j (cap p h j) := by
  rw [selfVis_ofOrd_iff, ← floor_limit p h, finitePart_limitPart_add_nat]

theorem clipped_proper (d : X) : clipped p h j d ≠ ⊤ :=
  by simp

theorem clipped_prefix (d : X) : min (clipped p h j d) (ofOrd h) = min (p d) (ofOrd h) := by grind [cutoff_lt_floor, floor_le_cap]

theorem clipped_literal (d : X) (hd : p d ≠ ⊤) : clipped p h j d = p d :=
  min_eq_left (((value_lt_floor p h d).resolve_right hd).le.trans (floor_le_cap p h j))

theorem collapse_clipped (d : X) : collapseBlock (floor p h) (clipped p h j d) = p d :=
  collapseBlock_min (floor_le_cap p h j) (value_lt_floor p h d)

private theorem grid_visible' : ∀ z ∈ ({cap p h j} : Finset ExtOrd), SelfVis j z := by
  simpa using cap_visible p h j

def decoder : ExtOrd → ExtOrd := collapseBlock (floor p h) ∘
  PairedSlotDecoder.decode j (values (clipped p h j)) {cap p h j} (cap p h j)

theorem decoder_witness : Witness (gTop j) (decoder p h j) :=
  Witness.comp_of_bottom_reflecting
    (PairedSlotDecoder.decode_witness (grid_visible' p h j) (cap_visible p h j))
    (collapseBlock_witness j (floor_limit p h)) le_rfl (collapseBlock_reflects_bottom _)

theorem decoder_read (d : X) : decoder p h j (normalize j (clipped p h j) d) = p d := by
  unfold decoder
  rw [Function.comp_apply, PairedSlotDecoder.decode_normalize (grid_visible' p h j)
    (cap_visible p h j) (clipped_proper p h j)]
  exact collapse_clipped p h j d

theorem decoder_supported (x : ExtOrd) :
    OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) p (decoder p h j x) := by
  unfold decoder
  rw [Function.comp_apply]
  rcases PairedSlotDecoder.decode_supported (j := j) (K := j) (p := clipped p h j)
      le_rfl (Finset.mem_singleton_self (cap p h j)) x with hz | hβ | ⟨d, i, hi, he⟩
  · rw [hz]
    tauto
  · rw [Finset.mem_singleton.mp (Finset.mem_coe.mp hβ), collapseBlock_of_le (floor_le_cap p h j)]
    tauto
  · rw [he]
    rcases value_lt_floor p h d with hlt | ht
    · rw [show clipped p h j d = p d from min_eq_left (hlt.le.trans (floor_le_cap p h j)),
        collapseBlock_of_lt (evr_lt_of_lt_limit (floor_limit p h) hlt j i)]
      tauto
    · rw [clipped, ht, min_top_left, evr_eq_self_of_selfVis (cap_visible p h j) i,
        collapseBlock_of_le (floor_le_cap p h j)]
      tauto

/-- Admission only needs to be closed under clipping and finite normalization. -/
structure Context (S X : Type*) [Fintype X] where
  profile : S → X → ExtOrd
  admitted : ℕ → S → Prop
  clip : ExtOrd → S → S
  clip_profile : ∀ c s d, profile (clip c s) d = min (profile s d) c
  clip_closed : ∀ {j c s}, 1 ≤ j → SelfVis j c → c ≠ ⊥ → admitted j s → admitted j (clip c s)
  norm : ℕ → S → S
  norm_profile : ∀ j s d, profile (norm j s) d = normalize j (profile s) d
  norm_closed : ∀ {j s}, 1 ≤ j → admitted j s → admitted j (norm j s)

namespace Context

variable {S : Type*} {j : ℕ} (C : Context S X)

abbrev inserted (s : S) (j : ℕ) (h : Ordinal.{0}) := C.clip (cap (C.profile s) h j) s

abbrev encoded (s : S) (j : ℕ) (h : Ordinal.{0}) := C.norm j (C.inserted s j h)

theorem inserted_profile (s : S) (j : ℕ) (h : Ordinal.{0}) :
    C.profile (C.inserted s j h) = clipped (C.profile s) h j := funext (C.clip_profile _ _)

theorem encoded_profile (s : S) (j : ℕ) (h : Ordinal.{0}) :
    C.profile (C.encoded s j h) = normalize j (clipped (C.profile s) h j) := by
  rw [← C.inserted_profile s j h]
  exact funext (C.norm_profile _ _)

theorem encoded_admitted (hj : 1 ≤ j) {s : S} (hs : C.admitted j s) (h : Ordinal.{0}) :
    C.admitted j (C.encoded s j h) :=
  C.norm_closed hj (C.clip_closed hj (cap_visible _ _ _) (ofOrd_ne_bot _) hs)

theorem encoded_canonical (s : S) (j : ℕ) (h : Ordinal.{0}) :
    C.profile (C.encoded s j h) ∈ CanonicalPairedProfiles.inventory X j := by
  rw [C.encoded_profile]
  exact CanonicalPairedProfiles.normalize_mem_inventory _ _ (clipped_proper _ _ _)

theorem encoded_rank (s : S) (j : ℕ) (h : Ordinal.{0}) (d : X) :
    LadderScalarRendering.fieldRank (C.profile (C.encoded s j h)) d =
      LadderScalarRendering.fieldRank (C.profile s) d := by
  rw [C.encoded_profile]
  exact (ReceivingCatalogueRanks.fieldRank_normalize j _ (clipped_proper _ _ _) d).trans
    (ReceivingCatalogueRanks.fieldRank_of_leftInverse _ (fun _ _ ht => min_le_min_right _ ht)
      (collapseBlock_witness j (floor_limit (C.profile s) h)).mono (min_bot_left _)
      rfl (collapse_clipped _ _ _) d)

abbrev Anchor (j : ℕ) := ↥(CanonicalPairedProfiles.Realized X j C.profile (C.admitted j))

theorem rank_anchor (hj : 1 ≤ j) {s : S} (hs : C.admitted j s) :
    ∃ a : C.Anchor j, ∀ d, LadderScalarRendering.fieldRank a.val d = LadderScalarRendering.fieldRank (C.profile s) d :=
  ⟨⟨_, C.encoded_canonical s j 0, _, C.encoded_admitted hj hs 0, rfl⟩, C.encoded_rank s j 0⟩

theorem exists_supported_decoder (hj : 1 ≤ j) {s : S} (hs : C.admitted j s) :
    ∃ q : S, C.admitted j q ∧ C.profile q ∈ CanonicalPairedProfiles.inventory X j ∧
      ∃ δ, Witness (gTop j) δ ∧ (∀ d, δ (C.profile q d) = C.profile s d) ∧
        (∀ d, δ (C.profile q d) = ⊥ → C.profile q d = ⊥) ∧
        ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) (C.profile s) (δ x) := by
  refine ⟨C.encoded s j 0, C.encoded_admitted hj hs 0, C.encoded_canonical s j 0,
    decoder (C.profile s) 0 j, decoder_witness _ _ _, ?_, ?_, decoder_supported _ _ _⟩
  · rw [C.encoded_profile]
    exact decoder_read _ _ _
  · rw [C.encoded_profile]
    intro d hd
    rw [decoder_read] at hd
    exact (normalize_bot_iff _ _ _).mpr (by simp [clipped, hd])

/-- A canonical replacement whose decoder fixes the protected prefix. -/
structure ProtectedRepair (a : X → ExtOrd) (s : S) (j b : ℕ) where
  encoded : S
  admitted : C.admitted j encoded
  canonical : C.profile encoded ∈ CanonicalPairedProfiles.inventory X j
  prefix_eq : ∀ d, min (C.profile encoded d) (grid j b) = min (a d) (grid j b)
  decoder : ExtOrd → ExtOrd
  witness : Witness (gTop j) decoder
  readback : ∀ d, decoder (C.profile encoded d) = C.profile s d
  grid_fixed : ∀ i < b, decoder (grid j i) = grid j i
  reaches : grid j b ≤ decoder (grid j b)
  boundary_fixed : ∀ d, a d < grid j b → decoder (a d) = a d

/-- Native section supply and protected repair for fields read from an admitted profile. -/
structure Fibre {Y : Type*} (j : ℕ) (pick : Y → X) (legal : (Y → ExtOrd) → Prop) : Prop where
  lawful : ∀ {s}, C.admitted j s → legal (C.profile s ∘ pick)
  bottom : ∀ {p}, legal p → ∃ s, C.admitted j s ∧ ∀ d, C.profile s (pick d) = p d
  repair : ∀ {s b p}, C.admitted j s → C.profile s ∈ CanonicalPairedProfiles.inventory X j →
    legal p → (∀ d, min (p d) (grid j b) = min (C.profile s (pick d)) (grid j b)) →
    ∃ t, C.admitted j t ∧ (∀ d, C.profile t (pick d) = p d) ∧ Nonempty (C.ProtectedRepair (C.profile s) t j b)

theorem Fibre.reindex {C : Context S X} {Y : Type*} {pick read : Y → X} {legal : (Y → ExtOrd) → Prop}
    (F : C.Fibre j pick legal) (h : ∀ s, C.admitted j s → ∀ d, C.profile s (pick d) = C.profile s (read d)) :
    C.Fibre j read legal where
  lawful hs := Eq.mp (congrArg legal (funext (h _ hs))) (F.lawful hs)
  bottom hp := by
    obtain ⟨s, hs, hread⟩ := F.bottom hp
    exact ⟨s, hs, fun d => (h s hs d).symm.trans (hread d)⟩
  repair hs hc hp hag := by
    obtain ⟨s, hs, hread, hr⟩ := F.repair hs hc hp (fun d => (hag d).trans (congrArg (min · _) (h _ hs d).symm))
    exact ⟨s, hs, (fun d => (h s hs d).symm.trans (hread d)), hr⟩

private theorem grid_mono : Monotone (grid j) :=
  fun _ _ hi => ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)

theorem exists_protected_repair (hj : 1 ≤ j) {a : X → ExtOrd} {s : S} {b : ℕ}
    (ha : a ∈ CanonicalPairedProfiles.inventory X j) (hs : C.admitted j s)
    (hag : ∀ d, min (a d) (grid j b) = min (C.profile s d) (grid j b)) :
    Nonempty (C.ProtectedRepair a s j b) := by
  let h : Ordinal.{0} := Ordinal.omega0 * b + j
  let p := C.profile s
  have hagV : ∀ d, min (a d) (grid j b) = min (clipped p h j d) (grid j b) :=
    fun d => (hag d).trans (clipped_prefix p h j d).symm
  obtain ⟨κ, hw, hread, hfix, hreach, _⟩ := exists_supported_inverse ha (clipped_proper p h j) hagV
  let δ := collapseBlock (floor p h) ∘ κ
  have hcollapse := collapseBlock_witness j (floor_limit p h)
  have hδ := Witness.comp_of_bottom_reflecting hw hcollapse le_rfl (collapseBlock_reflects_bottom _)
  have hprefix : ∀ d, min (C.profile (C.encoded s j h) d) (grid j b) = min (a d) (grid j b) := by
    rw [C.encoded_profile]
    exact CanonicalPairedProfiles.normalize_cap X j ha hagV
  have hδread : ∀ d, δ (C.profile (C.encoded s j h) d) = p d := by
    rw [C.encoded_profile]
    intro d
    exact (congrArg (collapseBlock (floor p h)) (hread d)).trans (collapse_clipped p h j d)
  refine ⟨⟨C.encoded s j h, C.encoded_admitted hj hs h, C.encoded_canonical s j h,
    hprefix, δ, hδ, hδread, ?_, ?_, ?_⟩⟩
  · intro i hi
    dsimp only [δ, Function.comp_apply]
    rw [hfix i hi]
    exact collapseBlock_of_lt ((grid_mono hi.le).trans_lt (cutoff_lt_floor p h))
  · exact (collapseBlock_of_lt (cutoff_lt_floor p h)).ge.trans (hcollapse.mono hreach)
  grind

variable {C} in
theorem ProtectedRepair.grid_fixed_below {a : X → ExtOrd} {s : S} {b : ℕ}
    (r : C.ProtectedRepair a s j b) {z : ExtOrd} (hz : z ∈ sourceGrid j (Fintype.card X))
    (hlt : z < grid j b) : r.decoder z = z := by
  rcases Finset.mem_insert.mp hz with rfl | hz
  · exact r.witness.bot
  · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact r.grid_fixed i (lt_of_not_ge fun hi => (not_le_of_gt hlt) (grid_mono hi))

variable {C} in
theorem ProtectedRepair.decode_rows {a : X → ExtOrd} {s : S} {b : ℕ}
    (r : C.ProtectedRepair a s j b)
    {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    {sem : Semantics D} {q q' : D.below (A, j) → ExtOrd}
    (hq : RespectsSemanticsBelow sem (A, j) q) (hq' : RespectsSemanticsBelow sem (A, j) q')
    (hs : ∀ d, OrbitPrefixSupport.Supported j (sourceGrid j (Fintype.card X) : Set ExtOrd) a (q d))
    (hag : ∀ d, min (q' d) (grid j b) = min (q d) (grid j b)) :
    RespectsSemanticsBelow sem (A, j) (fun d => r.decoder (q' d)) ∧
      ∀ d, min (r.decoder (q' d)) (grid j b) = min (q d) (grid j b) :=
  OrbitPrefixSupport.decode_respects_of_positive_cut r.witness hq hq' (fun d => d.2.2)
    (grid_visible _ _) (ofOrd_ne_bot _) r.reaches (fun _ => r.grid_fixed_below) r.boundary_fixed hs hag

/-- A native cap-preserving patch supplies both operations, by using the bottom cap
for independent supply and then normalizing when the cut is protected. -/
theorem fibre_of_patch {Y : Type*} {pick : Y → X} {legal : (Y → ExtOrd) → Prop}
    (hj : 1 ≤ j) {z : S} (hz : C.admitted j z)
    (law : ∀ {s}, C.admitted j s → legal (C.profile s ∘ pick))
    (patch : ∀ {s p γ}, C.admitted j s → legal p → SelfVis j γ →
      (∀ d, min (p d) γ = min (C.profile s (pick d)) γ) →
      ∃ t, C.admitted j t ∧ (∀ d, C.profile t (pick d) = p d) ∧
        ∀ f, min (C.profile s f) γ = min (C.profile t f) γ) : C.Fibre j pick legal where
  lawful := law
  bottom hp := by
    obtain ⟨t, ht, he, -⟩ := patch hz hp (selfVis_bot j) (by simp)
    exact ⟨t, ht, he⟩
  repair hs hc hp hag := by
    obtain ⟨t, ht, he, hcap⟩ := patch hs hp (grid_visible j _) hag
    exact ⟨t, ht, he, C.exists_protected_repair hj hc ht hcap⟩

end Context

end

end VaughtConjecture.Knight.TerminalProfile
