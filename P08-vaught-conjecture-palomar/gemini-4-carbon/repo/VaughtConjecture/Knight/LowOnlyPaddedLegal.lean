/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyFibres
public import VaughtConjecture.Knight.CappedDonorNormalization
public import VaughtConjecture.Knight.CanonicalPairedProfiles
public import VaughtConjecture.Knight.SourcePrefixRows
public import VaughtConjecture.Knight.CappedDonorRepairPackage
public import VaughtConjecture.Knight.RelativeLadderRankRendering
public import VaughtConjecture.Knight.ReceivingRankLift
public import VaughtConjecture.Knight.ReceivingCatalogueRanks
public import VaughtConjecture.Knight.RecursiveRungRendering
public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.PaddedTower
public import VaughtConjecture.Knight.PaddedFaceLift
public import VaughtConjecture.Knight.SeparatedLayerFace
public import VaughtConjecture.Knight.CappedLiftComposition
public import VaughtConjecture.Knight.OrderedFaceRestriction

@[expose] public section

namespace VaughtConjecture.Knight

namespace LowOnly
open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref SharpWitnessComposition
open CanonicalPairedInverse LadderScalarRendering RelativeLadderLayer ReceivingCatalogueRanks
open PairedSlotEncoding RecursiveRungRendering
noncomputable section

abbrev Field {n : ℕ} (P C : SemScheme n) := Cell P.scheme ⊕ (Cell C.scheme ⊕ Unit)

namespace State
variable {n : ℕ} {P C : SemScheme n}

def profile (S : State P C) : Field P C → ExtOrd
  | .inl d => S.u d
  | .inr (.inl d) => S.v d
  | .inr (.inr _) => S.b

def ofProfile (a : Field P C → ExtOrd) : State P C :=
  ⟨fun d => a (.inl d), fun d => a (.inr (.inl d)), a (.inr (.inr ()))⟩

@[simp] theorem ofProfile_profile (S : State P C) : ofProfile S.profile = S := rfl

@[simp] theorem profile_ofProfile (a : Field P C → ExtOrd) : (ofProfile a).profile = a := by
  funext f; rcases f with d | d | ⟨⟩ <;> rfl

theorem profile_injective : Function.Injective (profile (P := P) (C := C)) :=
  fun _ _ h => congrArg ofProfile h

def map (σ : ExtOrd → ExtOrd) (S : State P C) : State P C :=
  ⟨fun d => σ (S.u d), fun d => σ (S.v d), σ S.b⟩

theorem profile_map (σ : ExtOrd → ExtOrd) (S : State P C) (d : Field P C) :
    (S.map σ).profile d = σ (S.profile d) := by
  rcases d with d | d | d <;> rfl

theorem capEq_iff_profile {S S' : State P C} {γ : ExtOrd} :
    S.CapEq γ S' ↔ ∀ d, min (S'.profile d) γ = min (S.profile d) γ :=
  ⟨fun ⟨hu, hv, hb⟩ => fun | .inl d => hu d | .inr (.inl d) => hv d | .inr (.inr _) => hb,
   fun h => ⟨fun d => h (.inl d), fun d => h (.inr (.inl d)), h (.inr (.inr ()))⟩⟩

def encoder (j : ℕ) (S : State P C) : ExtOrd → ExtOrd :=
  PairedSlotIncoming.encoder j (PairedSlotEncoding.values S.profile)

def normalize (j : ℕ) (S : State P C) : State P C := S.map (S.encoder j)

theorem profile_normalize (j : ℕ) (S : State P C) (d : Field P C) :
    (S.normalize j).profile d = PairedSlotEncoding.normalize j S.profile d :=
  (profile_map _ S d).trans (PairedSlotIncoming.encoder_profile j S.profile d)
end State

namespace Family
variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

theorem maximum_map {j : ℕ} {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop j) σ)
    (S : State P C) : F.maximum (S.map σ) = σ (F.maximum S) := by
  classical
  unfold maximum nonTopMax
  rw [Finset.apply_sup_eq_sup_comp σ (fun _ _ => hσ.mono.map_max) hσ.bot]; rfl

theorem Admissible.map {j : ℕ} {S : State P C} (hS : F.Admissible j S)
    {σ : ExtOrd → ExtOrd} (hσ : Witness (gTop j) σ) (hj : 1 ≤ j)
    (hbot : ∀ x, σ x = ⊥ → x = ⊥) : F.Admissible j (S.map σ) where
  lawfulP := map_respects_of_bottom_reflecting hS.lawfulP
    (fun d => d.2.2.trans (min_le_left _ _)) (boundedMap_of_witness hσ) hbot
  lawfulC := map_respects_of_bottom_reflecting hS.lawfulC
    (fun d => d.2.2.trans (min_le_left _ _)) (boundedMap_of_witness hσ) hbot
  shared a := congrArg σ (hS.shared a)
  futureP d hd := selfVis_map hσ hj (hS.futureP d hd)
  futureC d hd := selfVis_map hσ hj (hS.futureC d hd)
  cutoff := selfVis_map hσ (min_le_left _ _) hS.cutoff
  low hK hm d hd := by
    rw [F.maximum_map hσ] at hm
    have hm' : F.maximum S < S.b := lt_of_not_ge fun h => not_le.mpr hm (hσ.mono h)
    change max (σ S.b)
      (min (σ (S.v F.gap.c)) (extVisibilityReplace (σ (S.v F.gap.r.1)) K K)) ≤ σ (S.u d)
    rw [← map_comm hσ hK _ le_rfl, ← hσ.mono.map_min, ← hσ.mono.map_max]
    exact hσ.mono (hS.low hK hm' d hd)

theorem normalize_admissible {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) : F.Admissible j (S.normalize j) :=
  hS.map F (PairedSlotIncoming.encoder_witness j _) hj
    (PairedSlotIncoming.encoder_reflects_bottom j _)

theorem normalize_inventory (j : ℕ) {S : State P C} (hp : ∀ d, S.profile d ≠ ⊤) :
    (S.normalize j).profile ∈ CanonicalPairedProfiles.inventory (Field P C) j := by
  rw [show (S.normalize j).profile = PairedSlotEncoding.normalize j S.profile from
    funext (State.profile_normalize j S)]
  exact CanonicalPairedProfiles.normalize_mem_inventory _ _ hp

theorem exists_supported_decoder {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) :
    ∃ Q : State P C, F.Admissible j Q ∧
      Q.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j ∧
      ∃ δ : ExtOrd → ExtOrd, Witness (gTop j) δ ∧
        (∀ d, δ (Q.profile d) = S.profile d) ∧
        (∀ d, δ (Q.profile d) = ⊥ → Q.profile d = ⊥) ∧
        ∀ x, OrbitPrefixSupport.Supported j ({⊤} : Set ExtOrd) S.profile (δ x) := by
  obtain ⟨Q, hQ, hcanon, _, rest⟩ := exists_supported_decoder_of_map State.profile State.map
    State.normalize (F.Admissible j) State.profile_map State.profile_normalize hj hS
    (fun hf hb => hS.map F hf hj hb) (F.normalize_admissible hj)
  exact ⟨Q, hQ, hcanon, rest⟩

structure ProtectedRepair (a : Field P C → ExtOrd) (S : State P C) (j B : ℕ) where
  encoded : State P C
  admitted : F.Admissible j encoded
  canonical : encoded.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j
  prefix_eq : ∀ d, min (encoded.profile d) (grid j B) = min (a d) (grid j B)
  decoder : ExtOrd → ExtOrd
  witness : Witness (gTop j) decoder
  readback : ∀ d, decoder (encoded.profile d) = S.profile d
  grid_fixed : ∀ b < B, decoder (grid j b) = grid j b
  reaches : grid j B ≤ decoder (grid j B)
  boundary_fixed : ∀ d, a d < grid j B → decoder (a d) = a d

theorem exists_protected_repair {j B : ℕ} (hj : 1 ≤ j) {a : Field P C → ExtOrd}
    (ha : a ∈ CanonicalPairedProfiles.inventory (Field P C) j)
    {S : State P C} (hS : F.Admissible j S)
    (hag : ∀ d, min (a d) (grid j B) = min (S.profile d) (grid j B)) :
    Nonempty (F.ProtectedRepair a S j B) := by
  obtain ⟨Q, δ, hQ, hc, hp, hw, hr, hf, hreach, hb⟩ := exists_protected_repair_of_map
    State.profile State.map State.normalize (F.Admissible j) State.profile_map
    State.profile_normalize hj ha hS (fun hf hb => hS.map F hf hj hb)
    (F.normalize_admissible hj) hag
  exact ⟨⟨Q, hQ, hc, hp, δ, hw, hr, hf, hreach, hb⟩⟩

theorem private_protected_repair {j B : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S)
    (hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j)
    {v : C.scheme.below (effC n j) → ExtOrd}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    (hag : ∀ d, min (v d) (grid j B) = min (S.lowerC j d) (grid j B)) :
    ∃ S', F.Admissible j S' ∧ S'.lowerC j = v ∧
      S.CapEq (grid j B) S' ∧ S.FutureEq j S' ∧
      Nonempty (F.ProtectedRepair S.profile S' j B) := by
  obtain ⟨S', hS', hv', hcap, hfuture⟩ :=
    F.private_lift hS hv ((grid_visible j B).mono (min_le_left _ _)) hag
  exact ⟨S', hS', hv', hcap, hfuture, F.exists_protected_repair hj hcanon hS'
    fun d => (State.capEq_iff_profile.mp hcap d).symm⟩

theorem donor_protected_repair {j B : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S)
    (hcanon : S.profile ∈ CanonicalPairedProfiles.inventory (Field P C) j)
    {u : P.scheme.below (effC n j) → ExtOrd}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    (hag : ∀ d, min (u d) (grid j B) = min (S.lowerP j d) (grid j B)) :
    ∃ S', F.Admissible j S' ∧ S'.lowerP j = u ∧
      S.CapEq (grid j B) S' ∧ S.FutureEq j S' ∧
      Nonempty (F.ProtectedRepair S.profile S' j B) := by
  obtain ⟨S', hS', hu', hcap, hfuture⟩ :=
    F.donor_lift hS hu ((grid_visible j B).mono (min_le_left _ _)) hag
  exact ⟨S', hS', hu', hcap, hfuture, F.exists_protected_repair hj hcanon hS'
    fun d => (State.capEq_iff_profile.mp hcap d).symm⟩

def catalogue (j : ℕ) : Set (Field P C → ExtOrd) :=
  {a | a ∈ CanonicalPairedProfiles.inventory (Field P C) j ∧
    ∃ S : State P C, F.Admissible j S ∧ S.profile = a}

theorem catalogue_finite (j : ℕ) : (F.catalogue j).Finite :=
  (CanonicalPairedProfiles.inventory_finite (Field P C) j).subset fun _ h => h.1

abbrev Anchor (j : ℕ) := {a // a ∈ F.catalogue j}

instance (j : ℕ) : Fintype (F.Anchor j) := (F.catalogue_finite j).fintype

def fields (j : ℕ) (a : F.Anchor j) : Field P C → ExtOrd := a.val

def ProtectedRepair.anchor {F : Family P C K} {j B : ℕ} {a : Field P C → ExtOrd} {S : State P C}
    (r : F.ProtectedRepair a S j B) : F.Anchor j :=
  ⟨r.encoded.profile, r.canonical, r.encoded, r.admitted, rfl⟩

theorem exists_rank_anchor {j : ℕ} (hj : 1 ≤ j) {S : State P C} (hs : F.Admissible j S) :
    ∃ a : F.Anchor j, ∀ d, fieldRank a.val d = fieldRank S.profile d := by
  obtain ⟨Q, hQ, hcanon, hrank, _⟩ := exists_supported_decoder_of_map State.profile State.map
    State.normalize (F.Admissible j) State.profile_map State.profile_normalize hj hs
    (fun hf hb => hs.map F hf hj hb) (F.normalize_admissible hj)
  exact ⟨⟨Q.profile, hcanon, Q, hQ, rfl⟩, hrank⟩

private def seedAnchor : F.Anchor 1 :=
  ⟨((zero : State P C).normalize 1).profile,
    normalize_inventory 1 (by rintro (_ | _ | _) <;> exact bot_ne_top),
    _, F.normalize_admissible le_rfl (F.zero_admissible 1), rfl⟩

private theorem lower_visible_one_aux {D : SemScheme n} {j : ℕ} {v : Cell D.scheme → ExtOrd}
    (hv : RespectsSemanticsBelow D.rows (effC n j) (fun d => v d.1))
    (hf : ∀ d, j < D.scheme.grade d → SelfVis 1 (v d)) (d : Cell D.scheme) :
    SelfVis 1 (v d) := by
  by_cases hd : D.scheme.grade d ≤ j
  · exact selfVis_mono (hv.orderly ⟨d, Finset.subset_univ _, le_min hd (gradeC_le d)⟩).symm
      (D.scheme.grade_pos d)
  · exact hf d (Nat.lt_of_not_ge hd)

theorem Admissible.profile_visible_one {S : State P C} (hS : F.Admissible 1 S)
    (d : Field P C) : SelfVis 1 (S.profile d) := by
  rcases d with d | d | d
  · exact lower_visible_one_aux hS.lawfulP hS.futureP d
  · exact lower_visible_one_aux hS.lawfulC hS.futureC d
  · exact selfVis_mono hS.cutoff (le_min le_rfl F.gap.K_pos)

theorem anchor_visible_one (a : F.Anchor 1) (d : Field P C) : SelfVis 1 (F.fields 1 a d) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  change SelfVis 1 (a.val d); rw [← he]; exact hS.profile_visible_one F d

section GradeOneLayer
variable {ι : Type*} [DecidableEq ι] {A : Finset ι}
  (D : CellScheme A) (sem : Semantics D) (hA : 0 < A.card)
  (field : Cell D → Field P C) (hproper : ∀ d, D.scope d ≠ A)
  (hboundary : ∀ S : State P C, F.Admissible 1 S →
    RespectsSemanticsBelow sem (A, 1) (fun d => S.profile (field d.1)))

local notation "L" => carrier D hA (X := Field P C) (Q := F.Anchor 1)
local notation "E" => rows D sem hA field (F.fields 1) hproper

include hboundary in
private theorem anchor_boundary (b : F.Anchor 1) :
    RespectsSemanticsBelow sem (A, 1) (fun d => F.fields 1 b (field d.1)) := by
  obtain ⟨S, hs, he⟩ := b.property.2
  rw [show (fun d : D.below (A, 1) => F.fields 1 b (field d.1)) =
    fun d => S.profile (field d.1) from funext fun d => (congrFun he _).symm]
  exact hboundary S hs

def privateAt (incl : C.scheme.below (effC n 1) → D.below (A, 1))
    (d : C.scheme.below (effC n 1)) : (L).below (A, 1) :=
  ⟨old D hA (incl d).1, by rw [old_index]; exact (incl d).2⟩

def donorAt (incl : P.scheme.below (effC n 1) → D.below (A, 1))
    (d : P.scheme.below (effC n 1)) : (L).below (A, 1) :=
  ⟨old D hA (incl d).1, by rw [old_index]; exact (incl d).2⟩

include hboundary in
theorem exists_physical_section {S : State P C} (hs : F.Admissible 1 S) :
    ∃ w : (L).below (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      ∀ d : D.below (A, 1), w ⟨old D hA d.1, by rw [old_index]; exact d.2⟩ =
        S.profile (field d.1) := by
  obtain ⟨a, ha⟩ := F.exists_rank_anchor le_rfl hs
  exact ⟨fun d => renderWith D hA field (F.fields 1) a S.profile ⊤ d.1,
    renderWith_respects D sem hA field (F.fields 1) hproper a S.profile ha
      (fun _ => le_top) (hs.profile_visible_one F) (extVisibilityReplace_top 1 1)
      (hboundary S hs),
    fun d => renderWith_old D hA field (F.fields 1) a S.profile ⊤ ha d.1⟩

include hboundary in
theorem private_positive_lift (incl : C.scheme.below (effC n 1) → D.below (A, 1))
    (hfield : ∀ (S : State P C), F.Admissible 1 S → ∀ d, S.profile (field (incl d).1) = S.v d.1)
    {p : C.scheme.below (effC n 1) → ExtOrd} {q : (L).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow C.rows (effC n 1) p) (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (privateAt F D hA incl d)) γ = min (p d) γ) :
    ∃ w : (L).below (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (privateAt F D hA incl d) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ :=
  ReceivingRankLift.face_positive_lift D sem hA field (F.fields 1) hproper
    (anchor_boundary F D sem field hboundary) (fun a => a.property.1) F.anchor_visible_one
    F.seedAnchor (fun d => d.2.2.trans (min_le_left _ _)) incl (fun d => .inr (.inl d))
    (fun a d => by
      obtain ⟨S, hs, he⟩ := a.property.2
      change a.val (field (incl d).1) = a.val (.inr (.inl d.1)); rw [← he]; exact hfield S hs d)
    (fun a => by
      obtain ⟨S, hS, heS⟩ := a.property.2
      exact (funext fun d : C.scheme.below (effC n 1) =>
        (congrFun heS (.inr (.inl d.1))).symm) ▸ hS.lawfulC)
    (fun a {p' B} hp' hcap => by
      obtain ⟨S, hS, heS⟩ := a.property.2
      obtain ⟨T, _, hT, _, _, ⟨r⟩⟩ := F.private_protected_repair le_rfl hS
        (heS.symm ▸ a.property.1) hp' fun d => by
          rw [show S.lowerC 1 d = F.fields 1 a (.inr (.inl d.1)) from
            congrFun heS (.inr (.inl d.1))]; exact hcap d
      exact ⟨r.anchor, r.decoder, r.witness,
        fun d => (r.readback (.inr (.inl d.1))).trans (congrFun hT d),
        fun x => (congrArg (fun z => min (z x) _) heS).symm.trans (r.prefix_eq x).symm⟩)
    hp hq hγ hpos hag

include hboundary in
theorem donor_positive_lift (incl : P.scheme.below (effC n 1) → D.below (A, 1))
    (hfield : ∀ (S : State P C), F.Admissible 1 S → ∀ d, S.profile (field (incl d).1) = S.u d.1)
    {p : P.scheme.below (effC n 1) → ExtOrd} {q : (L).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow P.rows (effC n 1) p) (hq : RespectsSemanticsBelow E (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ) (hpos : ⊥ < γ)
    (hag : ∀ d, min (q (donorAt F D hA incl d)) γ = min (p d) γ) :
    ∃ w : (L).below (A, 1) → ExtOrd, RespectsSemanticsBelow E (A, 1) w ∧
      (∀ d, w (donorAt F D hA incl d) = p d) ∧ ∀ d, min (w d) γ = min (q d) γ :=
  ReceivingRankLift.face_positive_lift D sem hA field (F.fields 1) hproper
    (anchor_boundary F D sem field hboundary) (fun a => a.property.1) F.anchor_visible_one
    F.seedAnchor (fun d => d.2.2.trans (min_le_left _ _)) incl Sum.inl
    (fun a d => by
      obtain ⟨S, hs, he⟩ := a.property.2
      change a.val (field (incl d).1) = a.val (.inl d.1); rw [← he]; exact hfield S hs d)
    (fun a => by
      obtain ⟨S, hS, heS⟩ := a.property.2
      exact (funext fun d : P.scheme.below (effC n 1) =>
        (congrFun heS (.inl d.1)).symm) ▸ hS.lawfulP)
    (fun a {p' B} hp' hcap => by
      obtain ⟨S, hS, heS⟩ := a.property.2
      obtain ⟨T, _, hT, _, _, ⟨r⟩⟩ := F.donor_protected_repair le_rfl hS
        (heS.symm ▸ a.property.1) hp' fun d => by
          rw [show S.lowerP 1 d = F.fields 1 a (.inl d.1) from
            congrFun heS (.inl d.1)]; exact hcap d
      exact ⟨r.anchor, r.decoder, r.witness,
        fun d => (r.readback (.inl d.1)).trans (congrFun hT d),
        fun x => (congrArg (fun z => min (z x) _) heS).symm.trans (r.prefix_eq x).symm⟩)
    hp hq hγ hpos hag
end GradeOneLayer
end Family
end
end LowOnly

namespace LowOnlyRecursiveCharts
open Transform Value ExtOrd CappedDonor LowOnly PairedSlotEncoding RecursiveRungRendering
noncomputable section
variable {m K : ℕ} {P C : SemScheme m} (F : LowOnly.Family P C K)

theorem profile_visible_one {j : ℕ} (hj : 1 ≤ j) {S : State P C}
    (hS : F.Admissible j S) (d : Field P C) : SelfVis 1 (S.profile d) := by
  rcases d with d | d | d
  · by_cases hd : P.scheme.grade d ≤ j
    · exact selfVis_mono
        (hS.lawfulP.orderly ⟨d, Finset.subset_univ _, le_min hd (gradeC_le d)⟩).symm
        (P.scheme.grade_pos d)
    · exact hS.futureP d (Nat.lt_of_not_ge hd)
  · by_cases hd : C.scheme.grade d ≤ j
    · exact selfVis_mono
        (hS.lawfulC.orderly ⟨d, Finset.subset_univ _, le_min hd (gradeC_le d)⟩).symm
        (C.scheme.grade_pos d)
    · exact hS.futureC d (Nat.lt_of_not_ge hd)
  · exact selfVis_mono hS.cutoff (le_min hj F.gap.K_pos)

theorem anchor_proper {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    F.fields j a d ≠ ⊤ := a.property.1.2 d

theorem anchor_bound {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    F.fields j a d ≤ ceiling (Field P C) j :=
  (CanonicalPairedProfiles.inventory_bound _ _ a.property.1 d).trans
    (ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl))

theorem anchor_visible_one {j : ℕ} (hj : 1 ≤ j) (a : F.Anchor j) (d : Field P C) :
    SelfVis 1 (F.fields j a d) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  change SelfVis 1 (a.val d); rw [← he]; exact profile_visible_one F hj hS d
end
end LowOnlyRecursiveCharts

namespace LowOnlyRecursiveCoverage
open Transform Value ExtOrd CappedDonor LowOnly PairedSlotEncoding LowOnlyRecursiveCharts
noncomputable section
variable {m K : ℕ} {P C : SemScheme m} (F : LowOnly.Family P C K)

theorem admissible_down {i j : ℕ} (hj : 1 ≤ j) (hij : i ≤ j)
    {S : State P C} (hS : F.Admissible j S) : F.Admissible i S where
  lawfulP := hS.lawfulP.mono (CappedDonor.Ref.effC_mono hij)
  lawfulC := hS.lawfulC.mono (CappedDonor.Ref.effC_mono hij)
  shared := hS.shared
  futureP d _ := profile_visible_one F hj hS (.inl d)
  futureC d _ := profile_visible_one F hj hS (.inr (.inl d))
  cutoff := selfVis_mono hS.cutoff (min_le_min_right K hij)
  low hKi hm d hd := hS.low (hKi.trans hij) hm d hd

def normalizedAnchor {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    {S : State P C} (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤) : F.Anchor i :=
  ⟨(S.normalize i).profile, LowOnly.Family.normalize_inventory i hp,
    S.normalize i, F.normalize_admissible hi (admissible_down F (hi.trans hij) hij hS), rfl⟩

theorem normalizedAnchor_fields {i j : ℕ} (hi : 1 ≤ i) (hij : i ≤ j)
    {S : State P C} (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤) :
    F.fields i (normalizedAnchor F hi hij hS hp) = normalize i S.profile :=
  funext (State.profile_normalize i S)
end
end LowOnlyRecursiveCoverage

namespace LowOnlyOrderedLadder
open Transform Value ExtOrd AmalgamationPlan CappedDonor LowOnly RelativeLadderLayer
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)

def field (d : Cell I.boundary) : Field I.left I.right :=
  match (OrderedFaceBoundary.enumeration I.leftScheme I.rightScheme I.shared).symm d with
  | .inl c => .inl c
  | .inr c => .inr (.inl c.1)

theorem field_read (S : State I.left I.right) (d : Cell I.boundary) :
    S.profile (field I d) = I.paste S.u S.v d := by
  unfold field WholeDonorBoundary.Input.paste OrderedFaceBoundarySemantics.paste
  change S.profile (match (OrderedFaceBoundary.enumeration
      I.leftScheme I.rightScheme I.shared).symm d with
    | .inl c => .inl c
    | .inr c => .inr (.inl c.1)) = ProfileFaceUnion.paste I.shared.g S.u S.v
      ((OrderedFaceBoundary.enumeration I.leftScheme I.rightScheme I.shared).symm d)
  cases (OrderedFaceBoundary.enumeration I.leftScheme I.rightScheme I.shared).symm d <;> rfl

theorem field_donor (S : State I.left I.right) (d : Cell I.left.scheme) :
    S.profile (field I (I.leftFace.map d)) = S.u d :=
  (field_read I S (I.leftFace.map d)).trans (I.paste_left S.u S.v d)

include hroot in
theorem shared {S : State I.left I.right} (hs : F.root.Shared S.u S.v)
    (i : Cell I.common.scheme) : S.u (I.shared.f i) = S.v (I.shared.g i) := by
  obtain ⟨a, ha, hb⟩ := hroot i; exact ha ▸ hb ▸ hs a

include hroot in
theorem field_private {S : State I.left I.right} (hs : F.Admissible 1 S)
    (d : Cell I.right.scheme) : S.profile (field I (I.rightFace.map d)) = S.v d :=
  (field_read I S _).trans (I.paste_right S.u S.v (shared I F hroot hs.shared) d)

theorem proper (hB : B ⊂ A) (hC : C ⊂ A) (d : Cell I.boundary) : I.boundary.scope d ≠ A := by
  rcases OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared R I.isPlan
      I.leftPlan_le I.rightPlan_le d with ⟨d, rfl⟩ | ⟨d, rfl⟩
  · have hs := I.leftScheme.isPlan.subset_of_mem (I.leftScheme.scope_mem_plan d)
    change I.boundary.scope (I.leftFace.map d) ≠ A
    rw [show I.boundary.scope (I.leftFace.map d) = I.leftScheme.scope d from
      congrArg Prod.fst (I.leftFace.index d)]
    exact fun he => hB.not_ge (he ▸ hs)
  · have hs := I.rightScheme.isPlan.subset_of_mem (I.rightScheme.scope_mem_plan d)
    change I.boundary.scope (I.rightFace.map d) ≠ A
    rw [show I.boundary.scope (I.rightFace.map d) = I.rightScheme.scope d from
      congrArg Prod.fst (I.rightFace.index d)]
    exact fun he => hC.not_ge (he ▸ hs)

include hroot in
theorem boundary_lawful_at (j : ℕ) (S : State I.left I.right) (hs : F.Admissible j S) :
    RespectsSemanticsBelow I.rows (A, j) (fun d => S.profile (field I d.1)) := by
  let u := CellScheme.zeroAbove (S.lowerP j)
  let v := CellScheme.zeroAbove (S.lowerC j)
  have hshared (i : Cell I.common.scheme) : u (I.shared.f i) = v (I.shared.g i) := by
    have hg : I.left.scheme.grade (I.shared.f i) = I.right.scheme.grade (I.shared.g i) :=
      congrArg (fun x : Finset ι × ℕ => x.2) (I.shared.shared i)
    by_cases hd : I.left.scheme.grade (I.shared.f i) ≤ min j n
    · have he : I.right.scheme.grade (I.shared.g i) ≤ min j n := hg ▸ hd
      exact (CellScheme.zeroAbove_low (S.lowerP j) ⟨_, Finset.subset_univ _, hd⟩).trans
        ((shared I F hroot hs.shared i).trans
          (CellScheme.zeroAbove_low (S.lowerC j) ⟨_, Finset.subset_univ _, he⟩).symm)
    · exact (CellScheme.zeroAbove_high (S.lowerP j) hd).trans
        (CellScheme.zeroAbove_high (S.lowerC j) (hg ▸ hd)).symm
  have hl := (I.paste_respects hs.lawfulP.zeroAbove hs.lawfulC.zeroAbove hshared).toBelow (A, j)
  have he : (fun d : I.boundary.below (A, j) => S.profile (field I d.1)) =
      fun d => I.paste u v d.1 := by
    funext d; rw [field_read]
    rcases OrderedFaceBoundaryRows.covered I.leftScheme I.rightScheme I.shared R I.isPlan
        I.leftPlan_le I.rightPlan_le d.1 with ⟨c, hc⟩ | ⟨c, hc⟩
    · have hi : I.boundary.grade d.1 ≤ j := d.2.2
      rw [← hc] at hi ⊢
      have hg : I.left.scheme.grade c ≤ min j n :=
        le_min ((congrArg Prod.snd (I.leftFace.index c)).symm.trans_le hi) (gradeC_le c)
      exact (I.paste_left S.u S.v c).trans
        ((CellScheme.zeroAbove_low (S.lowerP j) ⟨c, Finset.subset_univ _, hg⟩).symm.trans
          (I.paste_left u v c).symm)
    · have hi : I.boundary.grade d.1 ≤ j := d.2.2
      rw [← hc] at hi ⊢
      have hg : I.right.scheme.grade c ≤ min j n :=
        le_min ((congrArg Prod.snd (I.rightFace.index c)).symm.trans_le hi) (gradeC_le c)
      exact (I.paste_right S.u S.v (shared I F hroot hs.shared) c).trans
        ((CellScheme.zeroAbove_low (S.lowerC j) ⟨c, Finset.subset_univ _, hg⟩).symm.trans
          (I.paste_right u v hshared c).symm)
  exact he ▸ hl

def privateIncl (d : I.right.scheme.below (effC n 1)) : I.boundary.below (A, 1) :=
  ⟨I.rightFace.map d.1, I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.rightFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩

def donorIncl (d : I.left.scheme.below (effC n 1)) : I.boundary.below (A, 1) :=
  ⟨I.leftFace.map d.1, I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
    (congrArg Prod.snd (I.leftFace.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩

include hroot in
theorem private_lift (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)
    {p : I.right.scheme.below (effC n 1) → ExtOrd}
    {q : (carrier I.boundary hA (X := Field I.left I.right) (Q := F.Anchor 1)).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.right.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper I hB hC)) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (Family.privateAt F I.boundary hA (privateIncl I) d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper I hB hC)) (A, 1) w ∧
      (∀ d, w (Family.privateAt F I.boundary hA (privateIncl I) d) = p d) ∧
      ∀ d, min (w d) γ = min (q d) γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨S, hs, he, _, _⟩ := F.private_bottom_supply hp
    obtain ⟨w, hw, hr⟩ := F.exists_physical_section I.boundary I.rows hA (field I)
      (proper I hB hC) (boundary_lawful_at I F hroot 1) hs
    exact ⟨w, hw, fun d => (hr (privateIncl I d)).trans
      ((field_private I F hroot hs d.1).trans (congrFun he d)),
      fun _ => by simp only [hz, min_bot_right]⟩
  · exact Family.private_positive_lift F I.boundary I.rows hA (field I) (proper I hB hC)
      (boundary_lawful_at I F hroot 1) (privateIncl I)
      (fun _ hs d => field_private I F hroot hs d.1) hp hq hγ (bot_lt_iff_ne_bot.mpr hz) hag

include hroot in
theorem donor_lift (hA : 0 < A.card) (hB : B ⊂ A) (hC : C ⊂ A)
    {p : I.left.scheme.below (effC n 1) → ExtOrd}
    {q : (carrier I.boundary hA (X := Field I.left I.right) (Q := F.Anchor 1)).below (A, 1) → ExtOrd}
    (hp : RespectsSemanticsBelow I.left.rows (effC n 1) p)
    (hq : RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper I hB hC)) (A, 1) q)
    {γ : ExtOrd} (hγ : SelfVis 1 γ)
    (hag : ∀ d, min (q (Family.donorAt F I.boundary hA (donorIncl I) d)) γ = min (p d) γ) :
    ∃ w, RespectsSemanticsBelow
      (rows I.boundary I.rows hA (field I) (F.fields 1) (proper I hB hC)) (A, 1) w ∧
      (∀ d, w (Family.donorAt F I.boundary hA (donorIncl I) d) = p d) ∧
      ∀ d, min (w d) γ = min (q d) γ := by
  by_cases hz : γ = ⊥
  · obtain ⟨S, hs, he, _, _⟩ := F.donor_bottom_supply hp
    obtain ⟨w, hw, hr⟩ := F.exists_physical_section I.boundary I.rows hA (field I)
      (proper I hB hC) (boundary_lawful_at I F hroot 1) hs
    exact ⟨w, hw, fun d => (hr (donorIncl I d)).trans
      ((field_donor I S d.1).trans (congrFun he d)),
      fun _ => by simp only [hz, min_bot_right]⟩
  · exact Family.donor_positive_lift F I.boundary I.rows hA (field I) (proper I hB hC)
      (boundary_lawful_at I F hroot 1) (donorIncl I)
      (fun S _ d => field_donor I S d.1) hp hq hγ (bot_lt_iff_ne_bot.mpr hz) hag
end
end LowOnlyOrderedLadder

namespace LowOnlyOrderedSources
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)

abbrev boundary_lawful_at := LowOnlyOrderedLadder.boundary_lawful_at I F hroot

include hroot in
theorem anchor_lawful (j : ℕ) (a : F.Anchor j) :
    RespectsSemanticsBelow I.rows (A, j) (fun d => F.fields j a (field I d.1)) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  exact (funext fun d => (congrFun he _).symm) ▸ boundary_lawful_at I F hroot j S hS
end
end LowOnlyOrderedSources

namespace LowSeparator
open Transform Value ExtOrd PairedSlotEncoding PairedSlotComparison SharpWitnessComposition
  SourcePrefixRows LowOnly
noncomputable section

section Scalar
variable {X : Type*} [Fintype X] (K : ℕ) (N : X → Prop) [DecidablePred N] (b : X)

def donorMax (s : X → ExtOrd) : ExtOrd := (Finset.univ.filter N).sup s

theorem le_donorMax (s : X → ExtOrd) {d : X} (hd : N d) : s d ≤ donorMax N s :=
  Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩)

theorem donorMax_le {s : X → ExtOrd} {c : ExtOrd} (h : ∀ d, N d → s d ≤ c) : donorMax N s ≤ c :=
  Finset.sup_le fun d hd => h d (Finset.mem_filter.mp hd).2

theorem donorMax_congr {s a : X → ExtOrd} (h : ∀ d, N d → a d = s d) :
    donorMax N a = donorMax N s :=
  Finset.sup_congr rfl fun d hd => h d (Finset.mem_filter.mp hd).2

theorem donorMax_ne_top {s : X → ExtOrd} (hs : ∀ d, s d ≠ ⊤) : donorMax N s ≠ ⊤ :=
  ne_of_lt ((Finset.sup_lt_iff bot_lt_top).mpr fun d _ => lt_top_iff_ne_top.mpr (hs d))

theorem donorMax_cases (s : X → ExtOrd) :
    donorMax N s = ⊥ ∨ ∃ d, N d ∧ s d = donorMax N s := by
  by_cases hne : (Finset.univ.filter N).Nonempty
  · obtain ⟨d, hd, he⟩ := Finset.exists_mem_eq_sup _ hne s
    exact Or.inr ⟨d, (Finset.mem_filter.mp hd).2, he.symm⟩
  · exact Or.inl (by unfold donorMax; rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sup_empty])

def cutoffCut (s : X → ExtOrd) : ExtOrd := extVisibilityReplace (donorMax N s) K K

theorem donorMax_le_cutoffCut (s : X → ExtOrd) : donorMax N s ≤ cutoffCut K N s :=
  TopSupport.le_evr_self _ _

theorem cutoffCut_selfVis (s : X → ExtOrd) : SelfVis K (cutoffCut K N s) :=
  TopSupport.selfVis_evr_self K _

theorem cutoffCut_ne_top {s : X → ExtOrd} (hs : ∀ d, s d ≠ ⊤) : cutoffCut K N s ≠ ⊤ :=
  TopSupport.evr_ne_top (donorMax_ne_top N hs) K K

def partner [DecidableEq X] (s : X → ExtOrd) : X → ExtOrd :=
  PairedSlotEncoding.normalize K (Function.update s b (cutoffCut K N s))

theorem cutoffCut_eq_endpoint {s : X → ExtOrd}
    (hs : s ∈ CanonicalPairedProfiles.inventory X K) :
    cutoffCut K N s = ⊥ ∨
      ∃ (m₀ : Ordinal.{0}) (d₀ : X), N d₀ ∧ s d₀ = ofOrd m₀ ∧ donorMax N s = ofOrd m₀ ∧
        m₀ = Ordinal.omega0 * block K (values s) m₀ + offset K (values s) m₀ ∧
        cutoffCut K N s = ofOrd (Ordinal.omega0 * block K (values s) m₀ + K) := by
  rcases ExtOrd.cases (donorMax N s) with hM | hM | ⟨m₀, hM⟩
  · exact Or.inl (by unfold cutoffCut; rw [hM]; rfl)
  · exact absurd hM (donorMax_ne_top N hs.2)
  · obtain ⟨d₀, hd₀, hd₀M⟩ : ∃ d, N d ∧ s d = donorMax N s :=
      (donorMax_cases N s).resolve_left fun h => (ofOrd_ne_bot m₀).symm (h.symm.trans hM)
    have hm₀ : s d₀ = ofOrd m₀ := hd₀M.trans hM
    have hcode : encode K (values s) m₀ = ofOrd m₀ := by
      have h := congrFun hs.1 d₀; rwa [PairedSlotEncoding.normalize_ofOrd hm₀, hm₀] at h
    have hdec : m₀ = Ordinal.omega0 * block K (values s) m₀ + offset K (values s) m₀ :=
      (ofOrd_inj.mp hcode).symm
    have hlim : limitPart m₀ = Ordinal.omega0 * block K (values s) m₀ := by
      conv_lhs => rw [hdec]
      exact limitPart_mul_add _ _
    have hfin : finitePart m₀ = offset K (values s) m₀ := by
      conv_lhs => rw [hdec]
      exact finitePart_mul_add _ _
    refine Or.inr ⟨m₀, d₀, hd₀, hm₀, hM, hdec, ?_⟩
    unfold cutoffCut; rw [hM]
    change extVisibilityReplace (ofOrd m₀) K K = _
    rcases lt_or_eq_of_le (offset_le K (values s) m₀) with hlt | heq
    · rw [extVisibilityReplace_of_finitePart_lt (hfin ▸ hlt) K, hlim]
    · rw [extVisibilityReplace_of_le_finitePart (by rw [hfin, heq]) K]
      conv_lhs => rw [hdec, heq]

private theorem encode_endpoint [DecidableEq X] {s : X → ExtOrd} {m₀ : Ordinal.{0}} {d₀ : X}
    (hm₀ : s d₀ = ofOrd m₀)
    (hdec : m₀ = Ordinal.omega0 * block K (values s) m₀ + offset K (values s) m₀)
    (hsb : ofOrd (Ordinal.omega0 * block K (values s) m₀ + K) < s b) :
    encode K (values (Function.update s b (ofOrd (Ordinal.omega0 * block K (values s) m₀ + K))))
      (Ordinal.omega0 * block K (values s) m₀ + K) =
      ofOrd (Ordinal.omega0 * block K (values s) m₀ + K) := by
  classical
  set S := values s with hSdef
  set bl := block K S m₀
  set off := offset K S m₀
  set h₀ : Ordinal.{0} := Ordinal.omega0 * bl + K with hh₀
  set T := values (Function.update s b (ofOrd h₀)) with hTdef
  set S' : Finset Ordinal.{0} := insert h₀ S with hS'def
  have hoff : off ≤ K := offset_le K S m₀
  have hm₀S : m₀ ∈ S := mem_values.mpr ⟨d₀, hm₀⟩
  have hh₀lim : limitPart h₀ = Ordinal.omega0 * bl := limitPart_mul_add _ _
  have hh₀fin : finitePart h₀ = K := finitePart_mul_add _ _
  have hm₀lim : limitPart m₀ = Ordinal.omega0 * bl := by rw [hdec]; exact limitPart_mul_add _ _
  have hm₀fin : finitePart m₀ = off := by rw [hdec]; exact finitePart_mul_add _ _
  have horb (c) : Orbit K S' c ↔ Orbit K S c :=
    ⟨fun ⟨hf, e, he, hej, hec⟩ => (Finset.mem_insert.mp he).elim
      (fun he0 => by rw [he0, hh₀fin] at hej; exact absurd hej (lt_irrefl K))
      (fun he0 => ⟨hf, e, he0, hej, hec⟩),
     fun ⟨hf, e, he, hej, hec⟩ => ⟨hf, e, Finset.mem_insert_of_mem he, hej, hec⟩⟩
  have hkey (c) : key K S' c = key K S c := by
    by_cases ho : Orbit K S c
    · simp only [key, ite_eq_left ho, ite_eq_left ((horb c).mpr ho)]
    · simp only [key, ite_eq_right ho, ite_eq_right (fun h => ho ((horb c).mp h))]
  have horb₀ : Orbit K S h₀ ↔ Orbit K S m₀ :=
    ⟨fun ⟨_, e, he, hej, hec⟩ => ⟨hm₀fin ▸ hoff, e, he, hej, hec.trans (hh₀lim.trans hm₀lim.symm)⟩,
     fun ⟨_, e, he, hej, hec⟩ => ⟨hh₀fin ▸ le_rfl, e, he, hej, hec.trans (hm₀lim.trans hh₀lim.symm)⟩⟩
  have hkey₀ : key K S h₀ = key K S m₀ := by
    by_cases ho : Orbit K S m₀
    · simp only [key, ite_eq_left ho, ite_eq_left (horb₀.mpr ho), hh₀lim, hm₀lim]
    · have hoffK : off = K := by_contra fun hne =>
        ho (orbit_of_invisible hm₀S (by rw [hm₀fin]; exact lt_of_le_of_ne hoff hne))
      rw [hdec, hoffK]
  have himg : PairedSlotEncoding.keys K S' = insert (key K S h₀) (PairedSlotEncoding.keys K S) := by
    change S'.image (key K S') = insert (key K S h₀) (S.image (key K S))
    rw [hS'def, Finset.image_insert, hkey h₀]
    exact congrArg _ (Finset.image_congr fun c _ => hkey c)
  have hrank' : PairedSlotEncoding.rank K S' h₀ = PairedSlotEncoding.rank K S m₀ := by
    unfold PairedSlotEncoding.rank
    rw [hkey h₀, hkey₀, himg, Finset.filter_insert,
      ite_eq_right (by rw [hkey₀]; exact lt_irrefl _)]
  set h' : Ordinal.{0} := Ordinal.omega0 * bl + ((K + 1 : ℕ) : Ordinal.{0}) with hh'
  have hh'fin : K ≤ finitePart h' := by rw [finitePart_mul_add]; exact Nat.le_succ K
  have hh₀h' : h₀ < h' := (add_lt_add_iff_left _).mpr (Nat.cast_lt.mpr (Nat.lt_succ_self K))
  have heq (c) (hc : c < h') : c ∈ T ↔ c ∈ S' := by
    rw [hTdef, mem_values, hS'def, Finset.mem_insert, hSdef, mem_values]
    refine ⟨fun ⟨d, hd⟩ => ?_, fun h => ?_⟩
    · by_cases hdb : d = b
      · subst hdb; rw [Function.update_self] at hd; exact Or.inl (ofOrd_inj.mp hd).symm
      · rw [Function.update_of_ne hdb] at hd; exact Or.inr ⟨d, hd⟩
    · rcases h with rfl | ⟨d, hd⟩
      · exact ⟨b, by rw [Function.update_self]⟩
      · by_cases hdb : d = b
        · subst hdb
          have hc' : c < h₀ + 1 := by
            rw [hh'] at hc; rw [hh₀]; rw [Nat.cast_succ, ← add_assoc] at hc; exact hc
          exact absurd (ofOrd_lt_ofOrd.mp (hd ▸ hsb)) (not_lt.mpr (Order.lt_add_one_iff.mp hc'))
        · exact ⟨d, by rw [Function.update_of_ne hdb]; exact hd⟩
  have hrankT := rank_congr_below hh'fin heq hh₀h'
  have horbT : Orbit K T h₀ ↔ Orbit K S' h₀ :=
    orbit_congr_below hh'fin heq (by rw [hh₀lim]; exact le_self_add.trans_lt hh₀h')
  have hblock : block K T h₀ = bl := by
    change block K T h₀ = block K S m₀; unfold block; rw [hrankT, hrank']
    by_cases ho : Orbit K S m₀
    · rw [ite_eq_left (((horbT.trans (horb h₀)).trans horb₀).mpr ho), ite_eq_left ho]
    · rw [ite_eq_right fun h => ho (((horbT.trans (horb h₀)).trans horb₀).mp h), ite_eq_right ho]
  have hoffT : offset K T h₀ = K := by unfold offset; split_ifs; exact hh₀fin; rfl
  unfold encode; rw [hblock, hoffT]

abbrev grid : Finset ExtOrd := sourceGrid K (Fintype.card X)
theorem grid_bot : (⊥ : ExtOrd) ∈ grid (X := X) K := sourceGrid_bot _ _

section PartnerProfile
variable [DecidableEq X] {s : X → ExtOrd} (hs : s ∈ CanonicalPairedProfiles.inventory X K)
  (hlt : cutoffCut K N s < s b)

include hs in
theorem partner_mem : partner K N b s ∈ CanonicalPairedProfiles.inventory X K := by
  refine CanonicalPairedProfiles.normalize_mem_inventory _ _ fun d => ?_
  by_cases hdb : d = b
  · subst hdb; rw [Function.update_self]; exact cutoffCut_ne_top K N hs.2
  · rw [Function.update_of_ne hdb]; exact hs.2 d

include hs hlt in
theorem partner_cutoff : partner K N b s b = cutoffCut K N s := by
  unfold partner
  rcases cutoffCut_eq_endpoint K N hs with h0 | ⟨m₀, _, -, hm₀, -, hdec, hend⟩
  · rw [h0]; exact (PairedSlotEncoding.normalize_bot_iff K _ b).mpr (by rw [Function.update_self])
  · rw [PairedSlotEncoding.normalize_ofOrd (by rw [Function.update_self, hend]), hend]
    exact encode_endpoint K b hm₀ hdec (hend ▸ hlt)

include hs hlt in
theorem partner_cap (d : X) :
    min (partner K N b s d) (cutoffCut K N s) = min (s d) (cutoffCut K N s) := by
  rcases cutoffCut_eq_endpoint K N hs with h0 | ⟨m₀, _, -, _, -, _, hend⟩
  · rw [h0, min_eq_right bot_le, min_eq_right bot_le]
  · unfold partner; rw [hend]
    refine CanonicalPairedProfiles.normalize_cap X K hs (fun e => ?_) d
    by_cases heb : e = b
    · subst heb; rw [Function.update_self, min_self, min_eq_right (hend ▸ hlt.le)]
    · rw [Function.update_of_ne heb]

include hs hlt in
theorem cut_partner : cut (grid (X := X) K) s (partner K N b s) = cutoffCut K N s := by
  refine le_antisymm (le_of_not_gt fun hgt => ?_) ?_
  · have hag := agree_cut (grid_bot (X := X) K) s (partner K N b s) b
    rw [partner_cutoff K N b hs hlt, min_eq_left hgt.le] at hag
    exact lt_irrefl _ (hag ▸ lt_min hlt hgt)
  · refine le_cut ?_ fun x => (partner_cap K N b hs hlt x).symm
    rcases cutoffCut_eq_endpoint K N hs with h0 | ⟨m₀, d₀, -, hm₀, -, -, hend⟩
    · rw [h0]; exact grid_bot K
    · rw [hend]; apply sourceGrid_endpoint
      have h1 := block_le_twice_card (j := K) (mem_values.mpr ⟨d₀, hm₀⟩)
      have h2 := values_card_le s; omega

include hs hlt in
theorem activation_of_chart_lt {a : X → ExtOrd} {σ : ExtOrd → ExtOrd} (hσ : Monotone σ)
    (h : σ (cut (grid (X := X) K) a (partner K N b s)) < σ (cut (grid (X := X) K) a s)) :
    donorMax N a = donorMax N s ∧ cutoffCut K N s < a b := by
  have hlt_cut : cut (grid (X := X) K) a (partner K N b s) < cut (grid (X := X) K) a s :=
    lt_of_not_ge fun hle => not_lt.mpr (hσ hle) h
  have h1 := cut_triangle (grid_bot (X := X) K) a s (partner K N b s)
  rw [cut_partner K N b hs hlt] at h1
  have hu : cutoffCut K N s < cut (grid (X := X) K) a s := by_contra fun hn =>
    lt_irrefl _ ((min_eq_left (not_lt.mp hn) ▸ h1).trans_lt hlt_cut)
  have hag := agree_cut (grid_bot (X := X) K) a s
  exact ⟨donorMax_congr N fun d hd =>
      (eq_of_cap_eq_lt (hag d).symm
        (((le_donorMax N s hd).trans (donorMax_le_cutoffCut K N s)).trans_lt hu)).symm,
    (hag b ▸ lt_min hlt hu).trans_le (min_le_left _ _)⟩
end PartnerProfile
end Scalar

section FamilySep
variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

def donorField : LowOnly.Field P C → Prop
  | .inl d => F.p d ≠ ⊤
  | .inr _ => False

noncomputable instance : DecidablePred (donorField F) := Classical.decPred _

abbrev cutoffField : LowOnly.Field P C := Sum.inr (Sum.inr ())

theorem maximum_eq_donorMax (S : State P C) :
    F.maximum S = donorMax (donorField F) S.profile := by
  unfold LowOnly.Family.maximum LowOnly.nonTopMax donorMax
  refine le_antisymm (Finset.sup_le fun d hd => ?_) (Finset.sup_le fun x hx => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
    exact le_donorMax (donorField F) S.profile (d := Sum.inl d) hd
  · have hx' : donorField F x := (Finset.mem_filter.mp hx).2
    rcases x with d | d | d
    · exact LowOnly.le_nonTopMax S.u hx'
    · exact hx'.elim
    · exact hx'.elim

def partnerState (S : State P C) : State P C :=
  (⟨S.u, S.v, cutoffCut K (donorField F) S.profile⟩ : State P C).normalize K

theorem partnerState_profile (S : State P C) :
    (partnerState F S).profile =
      partner K (donorField F) (cutoffField (P := P) (C := C)) S.profile := by
  funext d; unfold partnerState partner; rw [State.profile_normalize]
  exact congrArg (fun x => PairedSlotEncoding.normalize K x d)
    (funext fun | .inl _ | .inr (.inl _) | .inr (.inr _) => rfl)

theorem partnerState_mem {S : State P C}
    (hcan : S.profile ∈ CanonicalPairedProfiles.inventory (LowOnly.Field P C) K) :
    (partnerState F S).profile ∈ CanonicalPairedProfiles.inventory (LowOnly.Field P C) K := by
  rw [partnerState_profile]; exact partner_mem K (donorField F) cutoffField hcan

theorem partnerState_admissible {S : State P C} (hS : F.Admissible K S)
    (hlt : cutoffCut K (donorField F) S.profile < S.b) (hK : 1 ≤ K) :
    F.Admissible K (partnerState F S) := by
  have hm : F.maximum S < S.b := by
    rw [maximum_eq_donorMax]
    exact (donorMax_le_cutoffCut K (donorField F) S.profile).trans_lt hlt
  exact F.normalize_admissible hK
    ⟨⟨hS.lawfulP, hS.lawfulC, hS.shared, hS.futureP, hS.futureC⟩,
      by rw [min_self]; exact cutoffCut_selfVis K (donorField F) S.profile,
      fun hj _ d hd => (max_le_max hlt.le le_rfl).trans (hS.low hj hm d hd)⟩

theorem serving_readback {S A : State P C} (hA : F.Admissible K A)
    (hcan : S.profile ∈ CanonicalPairedProfiles.inventory (LowOnly.Field P C) K)
    (hlt : cutoffCut K (donorField F) S.profile < S.b) {σ : ExtOrd → ExtOrd}
    (hσ : Witness (gTop K) σ)
    (h : σ (cut (grid (X := LowOnly.Field P C) K) A.profile (partnerState F S).profile) <
      σ (cut (grid (X := LowOnly.Field P C) K) A.profile S.profile))
    (hc : σ (A.v F.gap.c) = ⊤) (hr : σ (A.v F.gap.r.1) = ⊤) (d : Cell P.scheme)
    (hd : F.p d = ⊤) : σ (A.u d) = ⊤ := by
  rw [partnerState_profile] at h
  obtain ⟨heq, hab⟩ := activation_of_chart_lt K (donorField F) cutoffField hcan hlt hσ.mono h
  have hm : F.maximum A < A.b := by
    rw [maximum_eq_donorMax, heq]
    exact (donorMax_le_cutoffCut K (donorField F) S.profile).trans_lt hab
  have h1 := hσ.mono ((le_max_right _ _).trans (hA.low le_rfl hm d hd))
  change σ (min (A.v F.gap.c) (extVisibilityReplace (A.v F.gap.r.1) K K)) ≤ σ (A.u d) at h1
  rw [hσ.mono.map_min, hσ.comm_gTop _ le_rfl, hc, hr, extVisibilityReplace_top, min_self] at h1
  exact top_le_iff.mp h1
end FamilySep
end
end LowSeparator

namespace LowOnlyPaddedContract
open Transform Value ExtOrd CappedDonor LowOnly
noncomputable section
section Catalogue
variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

def state {j : ℕ} (a : F.Anchor j) : State P C := State.ofProfile a.val
theorem state_admissible {j : ℕ} (a : F.Anchor j) : F.Admissible j (state F a) := by
  obtain ⟨S, hS, he⟩ := a.property.2
  have hs : state F a = S := State.profile_injective ((State.profile_ofProfile a.val).trans he.symm)
  exact hs.symm ▸ hS
theorem state_profile {j : ℕ} (a : F.Anchor j) : (state F a).profile = F.fields j a :=
  State.profile_ofProfile a.val
theorem state_proper {j : ℕ} (a : F.Anchor j) (d : Field P C) :
    (state F a).profile d ≠ ⊤ := by
  rw [state_profile]; exact LowOnlyRecursiveCharts.anchor_proper F a d
end Catalogue
end
end LowOnlyPaddedContract

namespace LowOnlyPaddedSuccessor
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder
noncomputable section

section Anchors
variable {n K : ℕ} {P C : SemScheme n} (F : LowOnly.Family P C K)

def baseAnchor (a : F.Anchor 2) : F.Anchor 1 := by
  refine ⟨PairedSlotEncoding.normalize 1 a.val, ?_⟩
  obtain ⟨S, hS, he⟩ := a.property.2
  have hp : ∀ d, S.profile d ≠ ⊤ := he ▸ a.property.1.2
  have h := (LowOnlyRecursiveCoverage.normalizedAnchor F le_rfl (by decide : 1 ≤ 2) hS hp).property
  change F.fields 1 (LowOnlyRecursiveCoverage.normalizedAnchor F le_rfl (by decide : 1 ≤ 2) hS hp) ∈
    F.catalogue 1 at h
  rw [LowOnlyRecursiveCoverage.normalizedAnchor_fields] at h
  simpa only [he] using h

theorem baseAnchor_ranks (a : F.Anchor 2) (d : Field P C) :
    RelativeLadderLayer.ranks (F.fields 1) (baseAnchor F a) d =
      LadderScalarRendering.fieldRank (F.fields 2 a) d :=
  ReceivingCatalogueRanks.fieldRank_normalize 1 a.val a.property.1.2 d
end Anchors

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

@[reducible] def cat : PaddedTower.Catalogue I where
  hA := hA
  Fld := Field I.left I.right
  St := State I.left I.right
  profile := State.profile
  Admissible := F.Admissible
  Anchor := F.Anchor
  fields := F.fields
  anchor_inv a := a.property.1
  field := field I
  proper := proper I hB hC
  birth_lawful := LowOnlyOrderedSources.anchor_lawful I F hroot 1
  incoming_lawful := LowOnlyOrderedSources.anchor_lawful I F hroot 2
  baseAnchor := baseAnchor F
  baseAnchor_ranks := baseAnchor_ranks F
  visible_one := LowOnlyRecursiveCharts.anchor_visible_one F (by decide)
  anchor_bound := LowOnlyRecursiveCharts.anchor_bound F
  profile_visible_one {_} hj {_} hS := LowOnlyRecursiveCharts.profile_visible_one F hj hS
  boundary_lawful_at j S hS := LowOnlyOrderedSources.boundary_lawful_at I F hroot j S hS
  normalized _ hk {_} hj _ hS hp := LowOnlyRecursiveCoverage.normalizedAnchor F hk hj hS hp
  normalized_fields _ hk {_} hj _ hS hp := LowOnlyRecursiveCoverage.normalizedAnchor_fields F hk hj hS hp
  state := LowOnlyPaddedContract.state F
  state_admissible := LowOnlyPaddedContract.state_admissible F
  state_profile := LowOnlyPaddedContract.state_profile F
  state_proper := LowOnlyPaddedContract.state_proper F
  zeroSt := ⟨fun _ => ⊥, fun _ => ⊥, ⊥⟩
  zero_admissible t := F.zero_admissible (t + 2)
  zero_proper f := by rcases f with _ | (_ | _) <;> exact bot_ne_top

abbrev input := PaddedTower.input (cat I F hroot hA hB hC)
abbrev carrier := PaddedTower.succCarrier (cat I F hroot hA hB hC)
abbrev rows := PaddedTower.succRows (cat I F hroot hA hB hC)
abbrev source := PaddedTower.succSource (cat I F hroot hA hB hC)
abbrev old := PaddedTower.succOld (cat I F hroot hA hB hC)
abbrev leaf := PaddedTower.succLeaf (cat I F hroot hA hB hC)
abbrev original := PaddedTower.succOriginal (cat I F hroot hA hB hC)
abbrev cell_cases := PaddedTower.succ_cell_cases (cat I F hroot hA hB hC)
abbrev leaf_index := PaddedTower.succ_leaf_index (cat I F hroot hA hB hC)
abbrev original_index := PaddedTower.succ_original_index (cat I F hroot hA hB hC)
abbrev inherited_row := PaddedTower.succ_inherited_row (cat I F hroot hA hB hC)
abbrev original_readback := PaddedTower.succ_original_readback (cat I F hroot hA hB hC)
abbrev leaf_row := PaddedTower.succ_leaf_row (cat I F hroot hA hB hC)
abbrev source_leaf := PaddedTower.succ_source_leaf (cat I F hroot hA hB hC)
abbrev source_lawful := PaddedTower.succ_source_lawful (cat I F hroot hA hB hC)
abbrev source_prefix := @PaddedTower.succ_source_prefix _ _ _ _ _ _ _ _ _ I (cat I F hroot hA hB hC)
abbrev source_supported := PaddedTower.succ_source_supported (cat I F hroot hA hB hC)
end
end LowOnlyPaddedSuccessor

namespace LowOnlyPaddedContract
open LowOnlyPaddedSuccessor
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev base := PaddedTower.base (cat I F hroot hA hB hC)
abbrev baseRows := PaddedTower.baseRows (cat I F hroot hA hB hC)
abbrev Layer := PaddedTower.Layer (cat I F hroot hA hB hC)
abbrev initial := PaddedTower.initial (cat I F hroot hA hB hC)
end
end LowOnlyPaddedContract

namespace LowOnlyPaddedStepRows
open Value ExtOrd LowOnlyPaddedSuccessor LowOnlyPaddedContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k)

abbrev grid := PaddedTower.stepGrid P
abbrev ceiling := PaddedTower.stepCeiling P
abbrev selected := PaddedTower.selected P

variable (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)
@[reducible] def carrier := PaddedTower.stepCarrier P hnext
@[reducible] def old := PaddedTower.stepOld P hnext
@[reducible] def controller := PaddedTower.stepController P hnext
@[reducible] def member := PaddedTower.stepMember P hk hnext
@[reducible] def data := PaddedTower.stepData P hk hnext
@[reducible] def rows := PaddedTower.stepRows P hk hnext
@[reducible] def source := PaddedTower.stepSource P hk hnext
theorem source_old (a : F.Anchor (k + 1)) (d : Cell P.carrier) :
    source P hk hnext a (old P hnext d) = selected P a d :=
  PaddedTower.step_source_old P hk hnext a d
abbrev source_new := PaddedTower.step_source_new P hk hnext
abbrev source_lawful := PaddedTower.step_source_lawful P hk hnext
abbrev source_supported := PaddedTower.step_source_supported P hk hnext
abbrev source_short := PaddedTower.step_source_short P hk hnext
abbrev source_agreement := @PaddedTower.step_source_agreement _ _ _ _ _ _ _ _ _ I (cat I F hroot hA hB hC) k P hk hnext
abbrev inherited_row := PaddedTower.step_inherited_row P hk hnext
end
end LowOnlyPaddedStepRows

namespace LowOnlyPaddedStepRendering
open Value ExtOrd LowOnly LowOnlyPaddedSuccessor LowOnlyPaddedContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

abbrev baseMap := PaddedTower.stepBaseMap P hnext
abbrev base_index := PaddedTower.step_base_index P hnext
abbrev base_respects := PaddedTower.step_base_respects P hk hnext
abbrev cell_cases := PaddedTower.step_cell_cases P hk hnext
abbrev higher_short := PaddedTower.step_higher_short P hk hnext
abbrev normalized {j : ℕ} (hj : k + 1 ≤ j) (S : State I.left I.right)
    (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤) : F.Anchor (k + 1) :=
  LowOnlyRecursiveCoverage.normalizedAnchor F (Nat.succ_pos k) hj hS hp
theorem normalized_fields {j : ℕ} (hj : k + 1 ≤ j) (S : State I.left I.right)
    (hS : F.Admissible j S) (hp : ∀ d, S.profile d ≠ ⊤) :
    F.fields (k + 1) (normalized hj S hS hp) = PairedSlotEncoding.normalize (k + 1) S.profile :=
  LowOnlyRecursiveCoverage.normalizedAnchor_fields F (Nat.succ_pos k) hj hS hp
end
end LowOnlyPaddedStepRendering

namespace LowOnlyPaddedIteration
open LowOnlyPaddedSuccessor LowOnlyPaddedContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev build := PaddedTower.build (cat I F hroot hA hB hC)
abbrev build_plan := PaddedTower.build_plan (cat I F hroot hA hB hC)
theorem build_consistent (t : ℕ) (ht : t + 2 ≤ A.card) :
    (build I F hroot hA hB hC t ht).rows.IsConsistent :=
  (build I F hroot hA hB hC t ht).consistent
end
end LowOnlyPaddedIteration

namespace LowOnlyPaddedInstallation
open LowOnlyPaddedSuccessor
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

abbrev build_coded := PaddedTower.build_coded (cat I F hroot hA hB hC)
abbrev face_map := @PaddedTower.buildFace_map _ _ _ _ _ _ _ _ _ I (cat I F hroot hA hB hC)
abbrev donorFace := PaddedTower.donorFace (cat I F hroot hA hB hC) hB
abbrev privateFace := PaddedTower.privateFace (cat I F hroot hA hB hC) hC
abbrev donor_order := PaddedTower.donor_order (cat I F hroot hA hB hC) hB
abbrev private_order := PaddedTower.private_order (cat I F hroot hA hB hC) hC
end
end LowOnlyPaddedInstallation

section Endpoints
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse
open LowOnlyPaddedSuccessor LowOnlyPaddedContract LowOnlyPaddedStepRows
open LowOnlyPaddedStepRendering LowOnlyPaddedIteration LowOnlyOrderedLadder PaddedFaceLift

namespace LowOnlyPaddedCharts
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem exists_chart {q : (LowOnlyPaddedSuccessor.carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hq : RespectsSemanticsBelow (LowOnlyPaddedSuccessor.rows I F hroot hA hB hC) (A, 2) q) :
    ∃ a : F.Anchor 2, ∃ σ : ExtOrd → ExtOrd, ∃ M : ExtOrd,
      Witness (gTop 2) σ ∧
      (∀ d, (LowOnlyPaddedSuccessor.carrier I F hroot hA hB hC).grade d.1 = 2 → q d ≤ M) ∧
      ∀ d, σ (LowOnlyPaddedSuccessor.source I F hroot hA hB hC a d.1) = min (q d) M := by
  obtain ⟨a₀, _⟩ := F.exists_rank_anchor (by decide : 1 ≤ 2) (F.zero_admissible 2)
  refine exists_installed_chart a₀ (leaf I F hroot hA hB hC)
    (LowOnlyPaddedSuccessor.source I F hroot hA hB hC)
    (leaf_index I F hroot hA hB hC) (leaf_row I F hroot hA hB hC) (fun c hc => ?_) hq
  rcases LowOnlyPaddedSuccessor.cell_cases I F hroot hA hB hC c with ⟨x, rfl⟩ | ⟨a, ha⟩
  · rw [SourceLayerCarrier.cell_toCell] at hc
    exact False.elim ((input I F hroot hA hB hC).separation x (hc.symm ▸ GradedLe.refl _))
  · exact ⟨a, ha⟩
end
end LowOnlyPaddedCharts

namespace LowOnlyPaddedSupply
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem decoded_lawful (a : F.Anchor 2) {δ : ExtOrd → ExtOrd} (hδ : Witness (gTop 2) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, 2) (fun d => δ (a.val (field I d.1)))) :
    RespectsSemanticsBelow (LowOnlyPaddedSuccessor.rows I F hroot hA hB hC) (A, 2)
      (fun d => δ (LowOnlyPaddedSuccessor.source I F hroot hA hB hC a d.1)) := by
  let J := input I F hroot hA hB hC
  let L := initial I F hroot hA hB hC
  have hl0 := decoded_renderWith_respects (B := I.boundary) (semB := I.rows) J.one
    (field I) (F.fields 1) (proper I hB hC) (baseAnchor F a) (F.fields 2 a) J.ceiling
    (J.bounded a) (J.visible a) ((J.grid_visible _ J.ceiling_mem).mono (by decide : 1 ≤ 2))
    (baseAnchor_ranks F a) (by decide : 1 ≤ 2) hδ hreflect horiginal
  have hl : RespectsSemanticsBelow J.lowerRows (A, 2)
      (fun d => δ (LowOnlyPaddedSuccessor.source I F hroot hA hB hC a
        (LowOnlyPaddedSuccessor.old I F hroot hA hB hC d.1))) := by
    have hl1 : RespectsSemanticsBelow J.lowerRows (A, 2) (fun d => δ (J.predecessor a d.1)) := hl0
    simpa only [J, LowOnlyPaddedSuccessor.source, LowOnlyPaddedSuccessor.old,
      LadderWeightedSuccessor.Input.source_old] using hl1
  exact decoded_layer_lawful (LowOnlyPaddedSuccessor.source_lawful I F hroot hA hB hC a) hδ
    L.baseMap L.base_index L.base_respects hl fun c _ => by
      rcases L.cases c with ⟨b, hb⟩ | ⟨hsc, hgr, _⟩
      · exact Or.inl ⟨b, hb⟩
      · exact Or.inr (L.higher_short c hsc hgr)

theorem exists_section {S : State I.left I.right} (hS : F.Admissible 2 S) :
    ∃ w, RespectsSemanticsBelow (LowOnlyPaddedSuccessor.rows I F hroot hA hB hC) (A, 2) w ∧
      ∀ d : I.boundary.below (A, 2),
        w ⟨LowOnlyPaddedSuccessor.original I F hroot hA hB hC d.1,
          by rw [LowOnlyPaddedSuccessor.original_index]; exact d.2⟩ = S.profile (field I d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, _⟩ := F.exists_supported_decoder (by decide) hS
  let a : F.Anchor 2 := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  exact ⟨_, decoded_lawful I F hroot hA hB hC a hδ hreflect
    (by simpa only [a, hread] using LowOnlyOrderedSources.boundary_lawful_at I F hroot 2 S hS),
    fun d => (congrArg δ (original_readback I F hroot hA hB hC a d.1)).trans (hread _)⟩
end
end LowOnlyPaddedSupply

namespace LowOnlyPaddedTwoReadback
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right 2)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem exists_top_chart
    {q : (LowOnlyPaddedSuccessor.carrier I F hroot hA hB hC).below (A, 2) → ExtOrd}
    (hq : RespectsSemanticsBelow (LowOnlyPaddedSuccessor.rows I F hroot hA hB hC) (A, 2) q)
    (htop : ∃ d, (LowOnlyPaddedSuccessor.carrier I F hroot hA hB hC).grade d.1 = 2 ∧ q d = ⊤) :
    ∃ a : F.Anchor 2, ∃ σ : ExtOrd → ExtOrd, Witness (gTop 2) σ ∧
      ∀ d, σ (LowOnlyPaddedSuccessor.source I F hroot hA hB hC a d.1) = q d := by
  obtain ⟨a, σ, M, hσ, hM, hread⟩ := LowOnlyPaddedCharts.exists_chart I F hroot hA hB hC hq
  obtain ⟨d, hd, ht⟩ := htop
  have hMt : M = ⊤ := top_le_iff.mp (ht ▸ hM d hd)
  exact ⟨a, σ, hσ, fun e => (hread e).trans (by rw [hMt, min_top_right])⟩
end
end LowOnlyPaddedTwoReadback

namespace LowOnlyPaddedStepDecode
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

def original (d : Cell I.boundary) : Cell (LowOnlyPaddedStepRows.carrier P hnext) :=
  LowOnlyPaddedStepRows.old P hnext (P.baseMap (RelativeLadderLayer.old I.boundary (by omega) d))

theorem original_index (d : Cell I.boundary) :
    (LowOnlyPaddedStepRows.carrier P hnext).cell (original P hnext d) = I.boundary.cell d := by
  rw [original, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index,
    P.base_index, RelativeLadderLayer.old_index]

theorem source_original (a : F.Anchor (k + 1)) (d : Cell I.boundary) :
    LowOnlyPaddedStepRows.source P hk hnext a (original P hnext d) =
      F.fields (k + 1) a (field I d) :=
  (PaddedTower.step_source_old P hk hnext a _).trans
    ((P.original_readback (Nat.le_succ k) (state F a) (state_admissible F a) (state_proper F a)
      (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ k))
      ((PairedSlotComparison.sourceGrid_visible
        (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
      (fun f => by
        dsimp only [LowOnlyPaddedSuccessor.cat]; rw [state_profile]
        exact LowOnlyRecursiveCharts.anchor_bound F a f) d).trans
      (congrFun (state_profile F a) (field I d)))

theorem leaf_row (a : F.Anchor (k + 1))
    (d : (LowOnlyPaddedStepRows.carrier P hnext).below
      ((LowOnlyPaddedStepRows.carrier P hnext).cell (controller P hnext a).1)) :
    (LowOnlyPaddedStepRows.rows P hk hnext).E (controller P hnext a).1 d =
      LowOnlyPaddedStepRows.source P hk hnext a d.1 :=
  (data P hk hnext).row_new _ _
end
end LowOnlyPaddedStepDecode

namespace LowOnlyPaddedStepSupply
open LowOnlyPaddedStepDecode
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

def birth (a : F.Anchor (k + 1)) : F.Anchor 1 :=
  P.birth (Nat.le_succ k) (state F a) (state_admissible F a) (state_proper F a)

theorem birth_ranks (a : F.Anchor (k + 1)) (d : Field I.left I.right) :
    RelativeLadderLayer.ranks (F.fields 1) (birth P a) d =
      LadderScalarRendering.fieldRank (F.fields (k + 1) a) d := by
  rw [birth, P.birth_ranks]; dsimp only [LowOnlyPaddedSuccessor.cat]; rw [state_profile]

theorem source_base (a : F.Anchor (k + 1)) (d : Cell (base I F hroot hA hB hC)) :
    LowOnlyPaddedStepRows.source P hk hnext a (baseMap P hnext d) =
      RelativeLadderLayer.renderWith I.boundary (by omega : 0 < A.card)
        (field I) (F.fields 1) (birth P a) (F.fields (k + 1) a) (ceiling P) d := by
  have he := P.render_base (Nat.le_succ k) (state F a) (state_admissible F a) (state_proper F a)
    (G := LowOnlyPaddedStepRows.grid P) (H := ceiling P)
    (fun _ hz => (PairedSlotComparison.sourceGrid_visible hz).mono (Nat.le_succ k))
    ((PairedSlotComparison.sourceGrid_visible
      (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by
      dsimp only [LowOnlyPaddedSuccessor.cat]; rw [state_profile]
      exact LowOnlyRecursiveCharts.anchor_bound F a f) d
  exact (PaddedTower.step_source_old P hk hnext a (P.baseMap d)).trans
    (by simpa only [PaddedTower.selected, LowOnlyPaddedSuccessor.cat, birth, state_profile] using he)

theorem decoded_lawful (a : F.Anchor (k + 1)) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop (k + 1)) δ)
    (hreflect : ∀ f, δ (a.val f) = ⊥ → a.val f = ⊥)
    (horiginal : RespectsSemanticsBelow I.rows (A, k + 1) (fun d => δ (a.val (field I d.1)))) :
    RespectsSemanticsBelow (LowOnlyPaddedStepRows.rows P hk hnext) (A, k + 1)
      (fun d => δ (LowOnlyPaddedStepRows.source P hk hnext a d.1)) := by
  have hv1 : ∀ f, SelfVis 1 (F.fields (k + 1) a f) := by
    have := LowOnlyRecursiveCharts.profile_visible_one F (Nat.succ_pos k) (state_admissible F a)
    rwa [state_profile] at this
  have hl0 : RespectsSemanticsBelow (baseRows I F hroot hA hB hC) (A, k + 1)
      (fun d => δ (RelativeLadderLayer.renderWith I.boundary (by omega)
        (field I) (F.fields 1) (birth P a) (F.fields (k + 1) a) (ceiling P) d.1)) :=
    decoded_renderWith_respects (B := I.boundary) (semB := I.rows) (by omega)
      (field I) (F.fields 1) (proper I hB hC) (birth P a) (F.fields (k + 1) a) (ceiling P)
      (LowOnlyRecursiveCharts.anchor_bound F a) hv1
      ((PairedSlotComparison.sourceGrid_visible
        (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (by omega : 1 ≤ k + 1))
      (birth_ranks P a) (by omega : 1 ≤ k + 1) hδ hreflect horiginal
  exact decoded_layer_lawful (LowOnlyPaddedStepRows.source_lawful P hk hnext a) hδ
    (baseMap P hnext) (base_index P hnext) (base_respects P hk hnext)
    (by simpa only [source_base] using hl0) fun c _ => by
      rcases LowOnlyPaddedStepRendering.cell_cases P hk hnext c with ⟨b, hb⟩ | ⟨hsc, hgr, _⟩
      · exact Or.inl ⟨b, hb⟩
      · exact Or.inr (higher_short P hk hnext c hsc hgr)

theorem exists_section {S : State I.left I.right} (hS : F.Admissible (k + 1) S) :
    ∃ w, RespectsSemanticsBelow (LowOnlyPaddedStepRows.rows P hk hnext) (A, k + 1) w ∧
      ∀ d : I.boundary.below (A, k + 1),
        w ⟨LowOnlyPaddedStepDecode.original P hnext d.1,
          by rw [LowOnlyPaddedStepDecode.original_index]; exact d.2⟩ =
          S.profile (field I d.1) := by
  obtain ⟨Q, hQ, hcanon, δ, hδ, hread, hreflect, _⟩ :=
    F.exists_supported_decoder (Nat.succ_pos k) hS
  let a : F.Anchor (k + 1) := ⟨Q.profile, hcanon, Q, hQ, rfl⟩
  exact ⟨_, decoded_lawful P hk hnext a hδ hreflect
    (by simpa only [a, hread] using LowOnlyOrderedSources.boundary_lawful_at I F hroot (k + 1) S hS),
    fun d => (congrArg δ (source_original P hk hnext a d.1)).trans (hread _)⟩
end
end LowOnlyPaddedStepSupply

namespace LowOnlyPaddedStepChart
open LowOnlyPaddedStepDecode
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k) (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

def leafAt (a : F.Anchor (k + 1)) : (LowOnlyPaddedStepRows.carrier P hnext).below (A, k + 1) :=
  ⟨(controller P hnext a).1, (controller P hnext a).2.symm ▸ GradedLe.refl _⟩

theorem exists_chart
    {q : (LowOnlyPaddedStepRows.carrier P hnext).below (A, k + 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (LowOnlyPaddedStepRows.rows P hk hnext) (A, k + 1) q) :
    ∃ a : F.Anchor (k + 1), ∃ σ : ExtOrd → ExtOrd, ∃ M : ExtOrd,
      Witness (gTop (k + 1)) σ ∧
      (∀ d, (LowOnlyPaddedStepRows.carrier P hnext).grade d.1 = k + 1 → q d ≤ M) ∧
      ∀ d, σ (LowOnlyPaddedStepRows.source P hk hnext a d.1) = min (q d) M := by
  obtain ⟨a₀, _⟩ := F.exists_rank_anchor (Nat.succ_pos k) (F.zero_admissible (k + 1))
  refine exists_installed_chart a₀ (fun a => (controller P hnext a).1)
    (LowOnlyPaddedStepRows.source P hk hnext) (fun a => (controller P hnext a).2)
    (LowOnlyPaddedStepDecode.leaf_row P hk hnext) (fun c hc => ?_) hq
  let ctrl : SourcePrefixLayer.Controller (LowOnlyPaddedStepRows.carrier P hnext) (k + 1) := ⟨c, hc⟩
  exact ⟨member P hk hnext ctrl, congrArg Subtype.val
    ((SeparatedSourceLayerCarrier.controllerEquiv P.carrier (F.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext (P.separated (by omega))).apply_symm_apply ctrl).symm⟩

theorem exists_top_chart
    {q : (LowOnlyPaddedStepRows.carrier P hnext).below (A, k + 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (LowOnlyPaddedStepRows.rows P hk hnext) (A, k + 1) q)
    (htop : ∃ d, (LowOnlyPaddedStepRows.carrier P hnext).grade d.1 = k + 1 ∧ q d = ⊤) :
    ∃ a : F.Anchor (k + 1), ∃ σ : ExtOrd → ExtOrd, Witness (gTop (k + 1)) σ ∧
      ∀ d, σ (LowOnlyPaddedStepRows.source P hk hnext a d.1) = q d := by
  obtain ⟨a, σ, M, hσ, hM, hread⟩ := exists_chart P hk hnext hq
  obtain ⟨d, hd, ht⟩ := htop
  have hMt : M = ⊤ := top_le_iff.mp (ht ▸ hM d hd)
  exact ⟨a, σ, hσ, fun e => (hread e).trans (by rw [hMt, min_top_right])⟩
end
end LowOnlyPaddedStepChart

namespace LowOnlyPaddedEndpoints
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def original (t : ℕ) (ht : t + 2 ≤ A.card) (d : Cell I.boundary) :
    Cell (build I F hroot hA hB hC t ht).carrier :=
  (build I F hroot hA hB hC t ht).baseMap (RelativeLadderLayer.old I.boundary (by omega) d)

theorem original_index (t : ℕ) (ht : t + 2 ≤ A.card) (d : Cell I.boundary) :
    (build I F hroot hA hB hC t ht).carrier.cell (original I F hroot hA hB hC t ht d) =
      I.boundary.cell d :=
  ((build I F hroot hA hB hC t ht).base_index _).trans
    (RelativeLadderLayer.old_index I.boundary (by omega) d)
end
end LowOnlyPaddedEndpoints
end Endpoints

namespace LowOnlyPaddedLiftingInduction
open Transform Value ExtOrd CappedDonor LowOnly CanonicalPairedInverse
open LowOnlyPaddedSuccessor LowOnlyPaddedContract LowOnlyPaddedStepRows
open LowOnlyPaddedIteration LowOnlyOrderedLadder PaddedFaceLift
open AmalgamationPlan CoatomBoundaryExtension
noncomputable section

private def Through {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) (r : ℕ) : Prop :=
  ∀ {I J : Finset ι × ℕ}, I ∈ Plan.gradedPlan D.plan →
    J ∈ Plan.gradedPlan D.plan → (h : GradedLe I J) → J.2 ≤ r → CappedLift sem h

private theorem through_successor {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) {r : ℕ} (hprev : Through sem r)
    (hnext : ∀ (C B : Finset ι), (C, r + 1) ∈ Plan.gradedPlan D.plan →
      (B, r + 1) ∈ Plan.gradedPlan D.plan → (h : C ⊆ B) →
      CappedLift sem (show GradedLe (C, r + 1) (B, r + 1) from ⟨h, le_rfl⟩)) :
    Through sem (r + 1) := by
  rintro ⟨C, i⟩ ⟨B, j⟩ hC hB h hj
  by_cases hi : i ≤ r
  · have hBi : (B, i) ∈ Plan.gradedPlan D.plan := Plan.mem_gradedPlan.mpr
      ⟨(Plan.mem_gradedPlan.mp hB).1, (Plan.mem_gradedPlan.mp hC).2.1,
        h.2.trans (Plan.mem_gradedPlan.mp hB).2.2⟩
    exact (hprev hC hBi (show GradedLe (C, i) (B, i) from ⟨h.1, le_rfl⟩) hi).raise_target
      (h := h.1) h.2
  · obtain rfl : i = r + 1 := by have := h.2; dsimp only at hj this; omega
    obtain rfl : j = r + 1 := by have := h.2; dsimp only at hj this; omega
    exact hnext C B hC hB h.1

private theorem through_separated {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
    (sem : Semantics D) (Q : Type*) [Fintype Q] (k : ℕ) (hk : 0 < k) (hA : k ≤ A.card)
    (hs : ∀ d : Cell D, ¬ GradedLe (A, k) (D.cell d))
    (out : Semantics (SourceLayerCarrier.scheme D Q k hk hA))
    (hrow : ∀ (c : Cell D) (d : D.below (D.cell c)),
      out.E (SourceLayerCarrier.toCell D Q k hk hA (.inl c))
        (SeparatedSourceLayerCarrier.ownerEquiv D Q k hk hA hs c d) = sem.E c d)
    {r : ℕ} (hrk : r < k) (hprev : Through sem r) : Through out r :=
  fun hI hJ h hj => SeparatedLayerFace.lift D Q k hk hA hs sem out hrow h
    (fun hn => (not_le_of_gt hrk) (hn.2.trans hj)) (hprev hI hJ h hj)

section FullFace
variable {ι : Type*} [DecidableEq ι] {A V : Finset ι} {n : ℕ}
  (O : SemScheme n) (e : Fin n ↪ ι) (he : Finset.univ.image e = V)
  {D : CellScheme A} {sem : Semantics D}
  (G : ExactSemanticFace (PointImageSemantics.rows O.scheme e he O.rows) sem)

private def fullEquiv (j : ℕ) : O.scheme.below (effC n j) ≃ D.below (V, j) :=
  (show O.scheme.below (effC n j) ≃
      (AmalgamatedBoundary.pointImage O.scheme e he).below (V, j) from
    { toFun := fun d => ⟨d.1,
        (Finset.image_subset_image (Finset.subset_univ _)).trans he.subset,
        d.2.2.trans (min_le_left _ _)⟩
      invFun := fun d => ⟨d.1, Finset.subset_univ _, le_min d.2.2 (gradeC_le d.1)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans (G.belowEquiv (V, j) (Finset.Subset.refl _))

private theorem full_respects_iff (j : ℕ) (q : D.below (V, j) → ExtOrd) :
    RespectsSemanticsBelow sem (V, j) q ↔
      RespectsSemanticsBelow O.rows (effC n j) (q ∘ fullEquiv O e he G j) := by
  have h := respects_iff_of_equiv (sem' := O.rows) (sem := sem)
    (fullEquiv O e he G j) (fun d => (congrArg Prod.snd (G.index d.1)).symm)
    (fun d f => by
      change (O.scheme.cell d.1).1 ⊆ (O.scheme.cell f.1).1 ↔
        (D.cell (G.map d.1)).1 ⊆ (D.cell (G.map f.1)).1
      rw [G.index d.1, G.index f.1]; exact (Finset.image_subset_image_iff e.injective).symm)
    (fun c d _ => (G.row c.1 (PointImageSemantics.belowEquiv O.scheme e he c.1 d)).symm)
    (q ∘ fullEquiv O e he G j)
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm
end FullFace

section Tower
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

private def layerFace {k : ℕ} (P : Layer I F hroot hA hB hC k)
    {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows P.rows :=
  let L := SeparatedLayerFace.face I.boundary
    (RelativeLadderLayer.Point (X := Field I.left I.right) (Q := F.Anchor 1))
    1 Nat.one_pos (by omega) (RelativeLadderLayer.separated I.boundary (proper I hB hC))
    I.rows (baseRows I F hroot hA hB hC)
    (RelativeLadderLayer.inherited_row I.boundary I.rows (by omega)
      (field I) (F.fields 1) (proper I hB hC)) G hT
  { map := L.map.trans ⟨P.baseMap, P.base_mono.injective⟩
    index := fun d => (P.base_index _).trans (L.index d)
    exhaustive := fun z hz => by
      rcases P.cases z with ⟨d, rfl⟩ | ⟨hs, _, _⟩
      · obtain ⟨c, rfl⟩ := L.exhaustive d (by
          change (P.carrier.cell (P.baseMap d)).1 ⊆ T at hz; rwa [P.base_index] at hz)
        exact ⟨c, rfl⟩
      · exact False.elim (hT (hs ▸ hz))
    row := fun c d => (P.base_row (L.map c)
      ⟨L.map d.1, by rw [L.index, L.index]; exact d.2⟩).trans (L.row c d) }

private theorem inherited_on {D : CellScheme A} {sem : Semantics D}
    (dFace : ExactSemanticFace I.leftRows sem) (pFace : ExactSemanticFace I.rightRows sem)
    {U V : Finset ι × ℕ} (hU : U ∈ Plan.gradedPlan R) (hV : V ∈ Plan.gradedPlan R)
    (h : GradedLe U V) (hv : V.1 ⊆ B ∨ V.1 ⊆ C) : CappedLift sem h := by
  by_cases he : U = V
  · subst V; exact lift_refl
  rcases hv with hb | hc
  · exact dFace.lift hb (I.left_mem hU (h.1.trans hb)) (I.left_mem hV hb) h he
      (PointImageSemantics.bountiful _ _ _ _ I.left.complete I.left.bountiful)
  · exact pFace.lift hc (I.right_mem hU (h.1.trans hc)) (I.right_mem hV hc) h he
      (PointImageSemantics.bountiful _ _ _ _ I.right.complete I.right.bountiful)

private def lowerEquiv : (input I F hroot hA hB hC).lower.below (A, 1) ≃
    (LowOnlyPaddedSuccessor.carrier I F hroot hA hB hC).below (A, 1) :=
  HighLayerBountiful.equiv (input I F hroot hA hB hC).lower
    (F.Anchor 2)
    2 (by decide) hA (A, 1) (fun h => by have := h.2; omega)

private theorem lower_respects_iff (p : (input I F hroot hA hB hC).lower.below (A, 1) → ExtOrd) :
    RespectsSemanticsBelow (input I F hroot hA hB hC).lowerRows (A, 1) p ↔
      RespectsSemanticsBelow (LowOnlyPaddedSuccessor.rows I F hroot hA hB hC) (A, 1)
        (p ∘ (lowerEquiv I F hroot hA hB hC).symm) :=
  respects_iff_of_equiv (lowerEquiv I F hroot hA hB hC)
    (fun d => (congrArg Prod.snd (HighLayerBountiful.equiv_cell _ _ _ _ _ _ _ d)).symm)
    (fun _ _ => by simp only [CellScheme.scope, lowerEquiv, HighLayerBountiful.equiv_cell])
    (fun b d _ => (LowOnlyPaddedSuccessor.inherited_row I F hroot hA hB hC b.1 d).symm) p

private theorem init_side {V : Finset ι} (O : SemScheme n)
    (e₀ : Fin n ↪ ι) (he₀ : Finset.univ.image e₀ = V) (hV : V ⊂ A)
    (G : ExactSemanticFace (PointImageSemantics.rows O.scheme e₀ he₀ O.rows) I.rows)
    (pick : Cell O.scheme → Field I.left I.right)
    (sVal : State I.left I.right → O.scheme.below (effC n 2) → ExtOrd)
    (hs_law : ∀ S, F.Admissible 2 S → RespectsSemanticsBelow O.rows (effC n 2) (sVal S))
    (hs_eq : ∀ S, F.Admissible 2 S → ∀ d, S.profile (pick d.1) = sVal S d)
    (hfld : ∀ S, F.Admissible 2 S → ∀ c, S.profile (field I (G.map c)) = S.profile (pick c))
    (baseAt : O.scheme.below (effC n 1) → (input I F hroot hA hB hC).lower.below (A, 1))
    (hbase_val : ∀ d : O.scheme.below (effC n 1),
      (lowerEquiv I F hroot hA hB hC (baseAt d)).1 =
        LowOnlyPaddedSuccessor.original I F hroot hA hB hC (G.map d.1))
    (h1 : ∀ {p₀ : O.scheme.below (effC n 1) → ExtOrd}
      {q₀ : (input I F hroot hA hB hC).lower.below (A, 1) → ExtOrd} {M : ExtOrd},
      RespectsSemanticsBelow O.rows (effC n 1) p₀ →
      RespectsSemanticsBelow (input I F hroot hA hB hC).lowerRows (A, 1) q₀ → SelfVis 1 M →
      (∀ d, min (q₀ (baseAt d)) M = min (p₀ d) M) →
      ∃ r₀, RespectsSemanticsBelow (input I F hroot hA hB hC).lowerRows (A, 1) r₀ ∧
        (∀ d, r₀ (baseAt d) = p₀ d) ∧ ∀ d, min (r₀ d) M = min (q₀ d) M)
    (hbot : ∀ {p : O.scheme.below (effC n 2) → ExtOrd},
      RespectsSemanticsBelow O.rows (effC n 2) p → ∃ S, F.Admissible 2 S ∧ sVal S = p)
    (hprot : ∀ {S}, F.Admissible 2 S →
      S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) 2 →
      ∀ {b : ℕ} {v : O.scheme.below (effC n 2) → ExtOrd},
      RespectsSemanticsBelow O.rows (effC n 2) v →
      (∀ d, min (v d) (grid 2 b) = min (sVal S d) (grid 2 b)) →
      ∃ S', F.Admissible 2 S' ∧ sVal S' = v ∧ Nonempty (F.ProtectedRepair S.profile S' 2 b))
    {j : ℕ} (hj : j = 1 ∨ j = 2) :
    CappedLift (LowOnlyPaddedSuccessor.rows I F hroot hA hB hC)
      (show GradedLe (V, j) (A, j) from ⟨hV.subset, le_rfl⟩) := by
  let L := initial I F hroot hA hB hC
  let GL := layerFace I F hroot hA hB hC L G hV.not_ge
  rcases hj with rfl | rfl
  · intro p q γ hp hq hγ hag
    let e := lowerEquiv I F hroot hA hB hC
    let f := fullEquiv O e₀ he₀ GL 1
    have hq' : RespectsSemanticsBelow (input I F hroot hA hB hC).lowerRows (A, 1) (q ∘ e) := by
      apply (lower_respects_iff I F hroot hA hB hC _).mpr
      simpa only [e, Function.comp_def, Equiv.apply_symm_apply] using hq
    have hid (x) : e (baseAt x) =
        CellScheme.below.mono (show GradedLe (V, 1) (A, 1) from ⟨hV.subset, le_rfl⟩) (f x) :=
      Subtype.ext (hbase_val x)
    obtain ⟨r, hr, hread, hcap⟩ := h1 ((full_respects_iff O e₀ he₀ GL 1 p).mp hp) hq' hγ
      fun d => by change min (q (e (baseAt d))) γ = min (p (f d)) γ; rw [hid]; exact hag (f d)
    refine ⟨r ∘ e.symm, (lower_respects_iff I F hroot hA hB hC r).mp hr,
      fun d => by simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hcap (e.symm d),
      fun d => ?_⟩
    obtain ⟨x, rfl⟩ := f.surjective d
    exact (congrArg (r ∘ e.symm) (hid x).symm).trans
      ((congrArg r (e.symm_apply_apply _)).trans (hread x))
  · intro p q γ hp hq hγ hag
    let f := fullEquiv O e₀ he₀ GL 2
    let fAt (d : O.scheme.below (effC n 2)) :
        (LowOnlyPaddedSuccessor.carrier I F hroot hA hB hC).below (A, 2) :=
      ⟨LowOnlyPaddedSuccessor.original I F hroot hA hB hC (G.map d.1), by
        rw [LowOnlyPaddedSuccessor.original_index]
        exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
          (congrArg Prod.snd (G.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩⟩
    have hgr (d : O.scheme.below (effC n 2)) :
        (LowOnlyPaddedSuccessor.carrier I F hroot hA hB hC).grade (fAt d).1 = O.scheme.grade d.1 :=
      (congrArg Prod.snd (LowOnlyPaddedSuccessor.original_index I F hroot hA hB hC (G.map d.1))).trans
        (congrArg Prod.snd (G.index d.1))
    have hrest := fun {p u M} => restore_face (O := O) (effLow := effC n 1) (eff := effC n 2)
      (CappedDonor.Ref.effC_mono (by decide : 1 ≤ 2))
      (fun d => d.2.2.trans (min_le_left 2 n))
      (fun c hc => ⟨Finset.subset_univ _, le_min hc (gradeC_le c)⟩)
      baseAt fAt hgr (lowerEquiv I F hroot hA hB hC) (lower_respects_iff I F hroot hA hB hC)
      (fun d => Subtype.ext (hbase_val d))
      (fun p₀ q₀ M hp₀ hq₀ hM hag₀ => h1 hp₀ hq₀ hM hag₀) (p := p) (u := u) (M := M)
    obtain ⟨r, hr, hread, hcap⟩ := full_face_lift (by decide)
      (fun hn => by simp [effC, min_eq_left hn]) fAt hgr hrest
      State.profile (F.Admissible 2) Subtype.val Subtype.property
      (fun S hS hc => ⟨_, hc, S, hS, rfl⟩) (fun _ _ _ => rfl)
      (LowOnlyPaddedSuccessor.source I F hroot hA hB hC)
      (LowOnlyPaddedSuccessor.source_lawful I F hroot hA hB hC)
      (LowOnlyPaddedSuccessor.source_supported I F hroot hA hB hC)
      (fun b a {h} hh hba => LowOnlyPaddedSuccessor.source_prefix I F hroot hA hB hC b a hh hba)
      ((full_respects_iff O e₀ he₀ GL 2 p).mp hp) hq
      (fun hq' => LowOnlyPaddedCharts.exists_chart I F hroot hA hB hC hq')
      pick sVal hs_law hs_eq
      (fun a d => by
        obtain ⟨S, hS, he⟩ := a.property.2
        exact (original_readback I F hroot hA hB hC a (G.map d.1)).trans
          (by change a.val _ = _; rw [← he]; exact hfld S hS d.1))
      (fun _ {p'} hp' => by
        obtain ⟨S, hS, hr⟩ := hbot hp'
        obtain ⟨w, hw, hrd⟩ := LowOnlyPaddedSupply.exists_section I F hroot hA hB hC hS
        refine ⟨w, hw, fun d => ?_⟩
        have hd : GradedLe (I.boundary.cell (G.map d.1)) (A, 2) :=
          ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
            (congrArg Prod.snd (G.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩
        exact (hrd ⟨_, hd⟩).trans ((hfld S hS d.1).trans ((hs_eq S hS d).trans (congrFun hr d))))
      (fun _ {S} hS hc {b v} hv hagv => by
        obtain ⟨S', hS', he', ⟨r⟩⟩ := hprot hS hc hv hagv
        exact ⟨r.encoded, r.decoder, r.admitted, r.canonical, r.prefix_eq, r.witness,
          fun d => (r.readback (pick d.1)).trans ((hs_eq S' hS' d).trans (congrFun he' d)),
          r.grid_fixed, r.reaches, r.boundary_fixed⟩)
      hγ (fun d => hag (f d))
    refine ⟨r, hr, hcap, fun d => ?_⟩
    obtain ⟨x, rfl⟩ := f.surjective d; exact hread x

private theorem step_side {k : ℕ} (P : Layer I F hroot hA hB hC k)
    (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card) (hplan : P.carrier.plan = R)
    (hprev : Through P.rows k) (hface : k ≤ n)
    {V : Finset ι} (O : SemScheme n)
    (e₀ : Fin n ↪ ι) (he₀ : Finset.univ.image e₀ = V) (hV : V ⊂ A) (hVR : V ∈ R)
    (G : ExactSemanticFace (PointImageSemantics.rows O.scheme e₀ he₀ O.rows) I.rows)
    (pick : Cell O.scheme → Field I.left I.right)
    (sVal : State I.left I.right → O.scheme.below (effC n (k + 1)) → ExtOrd)
    (hs_law : ∀ S, F.Admissible (k + 1) S → RespectsSemanticsBelow O.rows (effC n (k + 1)) (sVal S))
    (hs_eq : ∀ S, F.Admissible (k + 1) S → ∀ d, S.profile (pick d.1) = sVal S d)
    (hfld : ∀ S, F.Admissible (k + 1) S → ∀ c, S.profile (field I (G.map c)) = S.profile (pick c))
    (hbot : ∀ {p : O.scheme.below (effC n (k + 1)) → ExtOrd},
      RespectsSemanticsBelow O.rows (effC n (k + 1)) p → ∃ S, F.Admissible (k + 1) S ∧ sVal S = p)
    (hprot : ∀ {S}, F.Admissible (k + 1) S →
      S.profile ∈ CanonicalPairedProfiles.inventory (Field I.left I.right) (k + 1) →
      ∀ {b : ℕ} {v : O.scheme.below (effC n (k + 1)) → ExtOrd},
      RespectsSemanticsBelow O.rows (effC n (k + 1)) v →
      (∀ d, min (v d) (grid (k + 1) b) = min (sVal S d) (grid (k + 1) b)) →
      ∃ S', F.Admissible (k + 1) S' ∧ sVal S' = v ∧
        Nonempty (F.ProtectedRepair S.profile S' (k + 1) b)) :
    CappedLift (LowOnlyPaddedStepRows.rows P hk hnext)
      (show GradedLe (V, k + 1) (A, k + 1) from ⟨hV.subset, le_rfl⟩) := by
  let GP := SeparatedLayerFace.face P.carrier (F.Anchor (k + 1)) (k + 1) (Nat.succ_pos k) hnext
    (P.separated (by omega)) P.rows (LowOnlyPaddedStepRows.rows P hk hnext)
    (LowOnlyPaddedStepRows.inherited_row P hk hnext)
    (layerFace I F hroot hA hB hC P G hV.not_ge) hV.not_ge
  let fLow := fun d => CellScheme.below.mono (show GradedLe (V, k) (A, k) from ⟨hV.subset, le_rfl⟩)
    (fullEquiv O e₀ he₀ GP k d)
  let fAt (d : O.scheme.below (effC n (k + 1))) :
      (LowOnlyPaddedStepRows.carrier P hnext).below (A, k + 1) :=
    ⟨LowOnlyPaddedStepDecode.original P hnext (G.map d.1), by
      rw [LowOnlyPaddedStepDecode.original_index]
      exact ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
        (congrArg Prod.snd (G.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩⟩
  have hgr (d : O.scheme.below (effC n (k + 1))) :
      (LowOnlyPaddedStepRows.carrier P hnext).grade (fAt d).1 = O.scheme.grade d.1 :=
    (congrArg Prod.snd (LowOnlyPaddedStepDecode.original_index P hnext (G.map d.1))).trans
      (congrArg Prod.snd (G.index d.1))
  have hcard : V.card = n := by
    rw [← he₀, Finset.card_image_of_injective _ e₀.injective, Finset.card_univ, Fintype.card_fin]
  have hVmem : (V, k) ∈ Plan.gradedPlan (LowOnlyPaddedStepRows.carrier P hnext).plan := by
    change (V, k) ∈ Plan.gradedPlan P.carrier.plan; rw [hplan]
    exact Plan.mem_gradedPlan.mpr ⟨hVR, by omega, by change k ≤ V.card; omega⟩
  have hAmem : (A, k) ∈ Plan.gradedPlan (LowOnlyPaddedStepRows.carrier P hnext).plan :=
    Plan.mem_gradedPlan.mpr ⟨(LowOnlyPaddedStepRows.carrier P hnext).isPlan.domain_mem,
      by omega, by change k ≤ A.card; omega⟩
  have hlow : Through (LowOnlyPaddedStepRows.rows P hk hnext) k :=
    through_separated P.rows (F.Anchor (k + 1)) (k + 1) (Nat.succ_pos k) hnext
      (P.separated (by omega)) (LowOnlyPaddedStepRows.rows P hk hnext)
      (LowOnlyPaddedStepRows.inherited_row P hk hnext) (Nat.lt_succ_self k) hprev
  have hcl := hlow hVmem hAmem ⟨hV.subset, le_rfl⟩ le_rfl
  have hrest := fun {p u M} => restore_face (O := O) (effLow := effC n k) (eff := effC n (k + 1))
    (CappedDonor.Ref.effC_mono (Nat.le_succ k))
    (fun d => d.2.2.trans (min_le_left (k + 1) n))
    (fun c hc => ⟨Finset.subset_univ _, le_min hc (gradeC_le c)⟩)
    fLow fAt hgr (Equiv.refl _) (fun _ => Iff.rfl) (fun _ => Subtype.ext rfl)
    (fun p₀ q₀ M hp₀ hq₀ hM hag₀ => by
      let e := fullEquiv O e₀ he₀ GP k
      obtain ⟨r₀, hr₀, hcap₀, hrd₀⟩ := hcl (p₀ ∘ e.symm) q₀ M
        (by
          apply (full_respects_iff O e₀ he₀ GP k _).mpr
          simpa only [e, Function.comp_def, Equiv.symm_apply_apply] using hp₀)
        hq₀ hM fun d => by
          obtain ⟨x, rfl⟩ := e.surjective d
          simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hag₀ x
      exact ⟨r₀, hr₀, fun x => by
        simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hrd₀ (e x), hcap₀⟩)
    (p := p) (u := u) (M := M)
  intro p q γ hp hq hγ hag
  let f := fullEquiv O e₀ he₀ GP (k + 1)
  have hid (d) : CellScheme.below.mono
      (show GradedLe (V, k + 1) (A, k + 1) from ⟨hV.subset, le_rfl⟩) (f d) = fAt d :=
    Subtype.ext rfl
  obtain ⟨r, hr, hread, hcap⟩ := full_face_lift (Nat.succ_pos k)
    (fun hn => by simp [effC, min_eq_left hn]) fAt hgr hrest
    State.profile (F.Admissible (k + 1)) Subtype.val Subtype.property
    (fun S hS hc => ⟨_, hc, S, hS, rfl⟩) (fun _ _ _ => rfl)
    (LowOnlyPaddedStepRows.source P hk hnext)
    (LowOnlyPaddedStepRows.source_lawful P hk hnext)
    (LowOnlyPaddedStepRows.source_supported P hk hnext)
    (fun b a {h} hh hba => LowOnlyPaddedStepRows.source_agreement P hk hnext b a hh hba)
    ((full_respects_iff O e₀ he₀ GP (k + 1) p).mp hp) hq
    (fun hq' => LowOnlyPaddedStepChart.exists_chart P hk hnext hq')
    pick sVal hs_law hs_eq
    (fun a d => by
      obtain ⟨S, hS, he⟩ := a.property.2
      exact (LowOnlyPaddedStepDecode.source_original P hk hnext a (G.map d.1)).trans
        (by change a.val _ = _; rw [← he]; exact hfld S hS d.1))
    (fun _ {p'} hp' => by
      obtain ⟨S, hS, hr⟩ := hbot hp'
      obtain ⟨w, hw, hrd⟩ := LowOnlyPaddedStepSupply.exists_section P hk hnext hS
      refine ⟨w, hw, fun d => ?_⟩
      have hd : GradedLe (I.boundary.cell (G.map d.1)) (A, k + 1) :=
        ⟨I.boundary.isPlan.subset_of_mem (I.boundary.scope_mem_plan _),
          (congrArg Prod.snd (G.index d.1)).le.trans (d.2.2.trans (min_le_left _ _))⟩
      exact (hrd ⟨_, hd⟩).trans ((hfld S hS d.1).trans ((hs_eq S hS d).trans (congrFun hr d))))
    (fun _ {S} hS hc {b v} hv hagv => by
      obtain ⟨S', hS', he', ⟨r⟩⟩ := hprot hS hc hv hagv
      exact ⟨r.encoded, r.decoder, r.admitted, r.canonical, r.prefix_eq, r.witness,
        fun d => (r.readback (pick d.1)).trans ((hs_eq S' hS' d).trans (congrFun he' d)),
        r.grid_fixed, r.reaches, r.boundary_fixed⟩)
    hγ (fun d => by simpa only [f, Function.comp_apply, hid] using hag (f d))
  refine ⟨r, hr, hcap, fun d => ?_⟩
  obtain ⟨x, rfl⟩ := f.surjective d; rw [hid]; exact hread x

variable (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)
include hcover

private theorem build_lifting (t : ℕ) (ht : t + 2 ≤ A.card) :
    Through (build I F hroot hA hB hC t ht).rows (t + 2) := by
  induction t with
  | zero =>
    let L := initial I F hroot hA hB hC
    let dFace := layerFace I F hroot hA hB hC L I.leftFace hB.not_ge
    let pFace := layerFace I F hroot hA hB hC L I.rightFace hC.not_ge
    intro ⟨S, i⟩ ⟨T, j⟩ hU hV h hj
    have hTi : (T, i) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
      ⟨(Plan.mem_gradedPlan.mp hV).1, (Plan.mem_gradedPlan.mp hU).2.1,
        h.2.trans (Plan.mem_gradedPlan.mp hV).2.2⟩
    have hi2 : i ≤ 2 := h.2.trans hj
    have hsame : CappedLift L.rows (show GradedLe (S, i) (T, i) from ⟨h.1, le_rfl⟩) := by
      by_cases htA : T = A
      · subst T
        by_cases hsA : S = A
        · subst S; exact lift_refl
        have hipos := (Plan.mem_gradedPlan.mp hU).2.1
        have hic : i = 1 ∨ i = 2 := by omega
        rcases hcover S (Plan.mem_gradedPlan.mp hU).1 hsA with hb | hc
        · have hBi : (B, i) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
            ⟨I.leftPlan_le I.leftScheme.isPlan.domain_mem, hipos,
              (Plan.mem_gradedPlan.mp hU).2.2.trans (Finset.card_le_card hb)⟩
          exact (inherited_on I dFace pFace hU hBi
            (show GradedLe (S, i) (B, i) from ⟨hb, le_rfl⟩) (Or.inl le_rfl)).comp
            (init_side I F hroot hA hB hC I.left I.placeLeft I.imageLeft hB I.leftFace
              Sum.inl (fun S => S.lowerP 2) (fun _ hS => hS.lawfulP) (fun _ _ _ => rfl)
              (fun S _ c => field_donor I S c)
              (Family.donorAt F I.boundary (by omega) (donorIncl I)) (fun _ => rfl)
              (fun hp₀ hq₀ hM hag₀ =>
                LowOnlyOrderedLadder.donor_lift I F hroot (by omega) hB hC hp₀ hq₀ hM hag₀)
              (fun {_} hp => by obtain ⟨S, hS, hr, _, _⟩ := F.donor_bottom_supply hp; exact ⟨S, hS, hr⟩)
              (fun {_} hS hc {_ _} hv hagv => by
                obtain ⟨S', hS', he', _, _, hr⟩ := F.donor_protected_repair (by decide) hS hc hv hagv
                exact ⟨S', hS', he', hr⟩) hic)
        · have hCi : (C, i) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
            ⟨I.rightPlan_le I.rightScheme.isPlan.domain_mem, hipos,
              (Plan.mem_gradedPlan.mp hU).2.2.trans (Finset.card_le_card hc)⟩
          exact (inherited_on I dFace pFace hU hCi
            (show GradedLe (S, i) (C, i) from ⟨hc, le_rfl⟩) (Or.inr le_rfl)).comp
            (init_side I F hroot hA hB hC I.right I.placeRight I.imageRight hC I.rightFace
              (fun d => .inr (.inl d)) (fun S => S.lowerC 2) (fun _ hS => hS.lawfulC)
              (fun _ _ _ => rfl)
              (fun _ hS c => field_private I F hroot
                (LowOnlyRecursiveCoverage.admissible_down F (by decide) (by decide) hS) c)
              (Family.privateAt F I.boundary (by omega) (privateIncl I)) (fun _ => rfl)
              (fun hp₀ hq₀ hM hag₀ =>
                LowOnlyOrderedLadder.private_lift I F hroot (by omega) hB hC hp₀ hq₀ hM hag₀)
              (fun {_} hp => by obtain ⟨S, hS, hr, _, _⟩ := F.private_bottom_supply hp; exact ⟨S, hS, hr⟩)
              (fun {_} hS hc {_ _} hv hagv => by
                obtain ⟨S', hS', he', _, _, hr⟩ := F.private_protected_repair (by decide) hS hc hv hagv
                exact ⟨S', hS', he', hr⟩) hic)
      · exact inherited_on I dFace pFace hU hTi
          (show GradedLe (S, i) (T, i) from ⟨h.1, le_rfl⟩)
          (hcover T (Plan.mem_gradedPlan.mp hV).1 htA)
    exact hsame.raise_target (h := h.1) h.2
  | succ t ih =>
    let P := build I F hroot hA hB hC t (by omega)
    have hplan := build_plan I F hroot hA hB hC t (by omega)
    have hprev : Through P.rows (t + 2) := ih (by omega)
    let k := t + 2
    have hk : 2 ≤ k := by omega
    have hlow : Through (LowOnlyPaddedStepRows.rows P hk ht) k :=
      through_separated P.rows (F.Anchor (k + 1)) (k + 1) (Nat.succ_pos k) ht
        (P.separated (by omega)) (LowOnlyPaddedStepRows.rows P hk ht)
        (LowOnlyPaddedStepRows.inherited_row P hk ht) (Nat.lt_succ_self k) hprev
    apply through_successor (LowOnlyPaddedStepRows.rows P hk ht) hlow
    intro S T hS hT hST
    change (S, k + 1) ∈ Plan.gradedPlan P.carrier.plan at hS
    change (T, k + 1) ∈ Plan.gradedPlan P.carrier.plan at hT
    rw [hplan] at hS hT
    let dFace := SeparatedLayerFace.face P.carrier (F.Anchor (k + 1)) (k + 1) (Nat.succ_pos k) ht
      (P.separated (by omega)) P.rows (LowOnlyPaddedStepRows.rows P hk ht)
      (LowOnlyPaddedStepRows.inherited_row P hk ht)
      (layerFace I F hroot hA hB hC P I.leftFace hB.not_ge) hB.not_ge
    let pFace := SeparatedLayerFace.face P.carrier (F.Anchor (k + 1)) (k + 1) (Nat.succ_pos k) ht
      (P.separated (by omega)) P.rows (LowOnlyPaddedStepRows.rows P hk ht)
      (LowOnlyPaddedStepRows.inherited_row P hk ht)
      (layerFace I F hroot hA hB hC P I.rightFace hC.not_ge) hC.not_ge
    by_cases htA : T = A
    · subst T
      by_cases hsA : S = A
      · subst S; exact lift_refl
      have hjpos := (Plan.mem_gradedPlan.mp hS).2.1
      rcases hcover S (Plan.mem_gradedPlan.mp hS).1 hsA with hb | hc
      · have hBj : (B, k + 1) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
          ⟨I.leftPlan_le I.leftScheme.isPlan.domain_mem, hjpos,
            (Plan.mem_gradedPlan.mp hS).2.2.trans (Finset.card_le_card hb)⟩
        have hcard : B.card = n := by
          rw [← I.imageLeft, Finset.card_image_of_injective _ I.placeLeft.injective,
            Finset.card_univ, Fintype.card_fin]
        have hface : k ≤ n := by
          have := (Plan.mem_gradedPlan.mp hBj).2.2; change k + 1 ≤ B.card at this; omega
        exact (inherited_on I dFace pFace hS hBj
          (show GradedLe (S, k + 1) (B, k + 1) from ⟨hb, le_rfl⟩) (Or.inl le_rfl)).comp
          (step_side I F hroot hA hB hC P hk ht hplan hprev hface
            I.left I.placeLeft I.imageLeft hB (I.leftPlan_le I.leftScheme.isPlan.domain_mem)
            I.leftFace Sum.inl (fun S => S.lowerP (k + 1)) (fun _ hS => hS.lawfulP)
            (fun _ _ _ => rfl) (fun S _ c => field_donor I S c)
            (fun {_} hp => by obtain ⟨S, hS, hr, _, _⟩ := F.donor_bottom_supply hp; exact ⟨S, hS, hr⟩)
            (fun {_} hS hc {_ _} hv hagv => by
              obtain ⟨S', hS', he', _, _, hr⟩ := F.donor_protected_repair (by omega) hS hc hv hagv
              exact ⟨S', hS', he', hr⟩))
      · have hCj : (C, k + 1) ∈ Plan.gradedPlan R := Plan.mem_gradedPlan.mpr
          ⟨I.rightPlan_le I.rightScheme.isPlan.domain_mem, hjpos,
            (Plan.mem_gradedPlan.mp hS).2.2.trans (Finset.card_le_card hc)⟩
        have hcard : C.card = n := by
          rw [← I.imageRight, Finset.card_image_of_injective _ I.placeRight.injective,
            Finset.card_univ, Fintype.card_fin]
        have hface : k ≤ n := by
          have := (Plan.mem_gradedPlan.mp hCj).2.2; change k + 1 ≤ C.card at this; omega
        exact (inherited_on I dFace pFace hS hCj
          (show GradedLe (S, k + 1) (C, k + 1) from ⟨hc, le_rfl⟩) (Or.inr le_rfl)).comp
          (step_side I F hroot hA hB hC P hk ht hplan hprev hface
            I.right I.placeRight I.imageRight hC (I.rightPlan_le I.rightScheme.isPlan.domain_mem)
            I.rightFace (fun d => .inr (.inl d)) (fun S => S.lowerC (k + 1))
            (fun _ hS => hS.lawfulC) (fun _ _ _ => rfl)
            (fun _ hS c => field_private I F hroot
              (LowOnlyRecursiveCoverage.admissible_down F (by omega) (by omega) hS) c)
            (fun {_} hp => by obtain ⟨S, hS, hr, _, _⟩ := F.private_bottom_supply hp; exact ⟨S, hS, hr⟩)
            (fun {_} hS hc {_ _} hv hagv => by
              obtain ⟨S', hS', he', _, _, hr⟩ := F.private_protected_repair (by omega) hS hc hv hagv
              exact ⟨S', hS', he', hr⟩))
    · exact inherited_on I dFace pFace hS hT
        (show GradedLe (S, k + 1) (T, k + 1) from ⟨hST, le_rfl⟩)
        (hcover T (Plan.mem_gradedPlan.mp hT).1 htA)

theorem full_bountiful :
    (build I F hroot hA hB hC (A.card - 2) (by omega)).rows.IsBountiful := by
  intro U V hU hV h _
  have hV' := Plan.mem_gradedPlan.mp hV
  have hscope := (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier.isPlan.subset_of_mem hV'.1
  have hb := hV'.2.2.trans (Finset.card_le_card hscope)
  exact build_lifting I F hroot hA hB hC hcover (A.card - 2) (by omega) hU hV h (by omega)

theorem full_complete :
    (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier.IsComplete := by
  intro ⟨T, j⟩ hJ
  have hJ' := Plan.mem_gradedPlan.mp hJ
  have hscope := (build I F hroot hA hB hC (A.card - 2) (by omega)).carrier.isPlan.subset_of_mem hJ'.1
  have hb := hJ'.2.2.trans (Finset.card_le_card hscope)
  rw [build_plan] at hJ
  by_cases he : T = A
  · subst T
    exact PaddedTower.full_occupied (cat I F hroot hA hB hC) (A.card - 2) (by omega) j
      (Plan.mem_gradedPlan.mp hJ).2.1 (by omega)
  · obtain ⟨d, hd⟩ := (I.occupied_iff hJ).mpr (hcover T (Plan.mem_gradedPlan.mp hJ).1 he)
    exact ⟨(build I F hroot hA hB hC (A.card - 2) (by omega)).baseMap
      (RelativeLadderLayer.old I.boundary (by omega) d),
      ((build I F hroot hA hB hC (A.card - 2) (by omega)).base_index _).trans
        ((RelativeLadderLayer.old_index I.boundary (by omega) d).trans hd)⟩
end Tower
end
end LowOnlyPaddedLiftingInduction

namespace LowOnlyPaddedPairLift
theorem cover_two_cofaces {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
    (s : AmalgamatedBoundaryPlan.Step A)
    (hR : R = s.plan) (hleft : B = A.erase s.a) (hright : C = A.erase s.b) :
    ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C := by
  intro S hS hs
  simp only [hR, AmalgamatedBoundaryPlan.Step.plan, Finset.mem_union, Finset.mem_singleton] at hS
  rcases hS with (hl | hr) | rfl
  · exact Or.inl (hleft ▸ s.left_plan.subset_of_mem hl)
  · exact Or.inr (hright ▸ s.right_plan.subset_of_mem hr)
  · exact False.elim (hs rfl)
end LowOnlyPaddedPairLift

namespace LowOnlyPaddedLegal
open Transform Value ExtOrd AmalgamationPlan LowOnly
open LowOnlyPaddedIteration LowOnlyPaddedInstallation
noncomputable section

theorem restrict_eq_of_face {a b : ℕ} (D : SemScheme a) (E : SemScheme b)
    (f : Fin a ↪ Fin b) {T : Finset (Fin b)} (hf : Finset.univ.image f = T)
    (G : ExactSemanticFace (PointImageSemantics.rows D.scheme f hf D.rows) E.rows)
    (hm : StrictMono G.map)
    (hp : Plan.restrictPlan E.scheme.plan T = D.scheme.plan.image (Finset.image f)) :
    E.restrictFace f (OrderedFaceRestriction.visible D E.scheme f hf hp) = D := by
  have he := OrderedFaceRestriction.scheme_eq D E.scheme E.rows f hf G hm hp
  exact SemScheme.ext_of_components (congrArg CellScheme.plan he)
    (congrArg CellScheme.card he) (CellScheme.cell_cast_of_eq he)
    (OrderedFaceRestriction.row_eq D E.scheme E.rows f hf G hm hp)

variable {l m n K : ℕ} {B C : Finset (Fin l)} {R : Finset (Finset (Fin l))}
  (I : WholeDonorBoundary.Input Finset.univ B C R m n n)
  (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ (Finset.univ : Finset (Fin l)).card)
  (hB : B ⊂ Finset.univ) (hC : C ⊂ Finset.univ)
  (hcover : ∀ S ∈ R, S ≠ Finset.univ → S ⊆ B ∨ S ⊆ C)

def semScheme : SemScheme l where
  scheme := (build I F hroot hA hB hC
    ((Finset.univ : Finset (Fin l)).card - 2) (by omega)).carrier
  rows := (build I F hroot hA hB hC
    ((Finset.univ : Finset (Fin l)).card - 2) (by omega)).rows
  rows_coded := build_coded I F hroot hA hB hC _ _
  consistent := build_consistent I F hroot hA hB hC _ _
  bountiful := LowOnlyPaddedLiftingInduction.full_bountiful I F hroot hA hB hC hcover
  complete := LowOnlyPaddedLiftingInduction.full_complete I F hroot hA hB hC hcover

local notation "E" => semScheme I F hroot hA hB hC hcover

theorem plan : (E).scheme.plan = R := build_plan I F hroot hA hB hC _ _

def donor : ExactSemanticFace I.leftRows (E).rows := donorFace I F hroot hA hB hC _ _

def privateFace : ExactSemanticFace I.rightRows (E).rows :=
  LowOnlyPaddedInstallation.privateFace I F hroot hA hB hC _ _

theorem donor_plan : Plan.restrictPlan (E).scheme.plan B =
    I.left.scheme.plan.image (Finset.image I.placeLeft) := by rw [plan]; exact I.planLeft

theorem private_plan : Plan.restrictPlan (E).scheme.plan C =
    I.right.scheme.plan.image (Finset.image I.placeRight) := by rw [plan]; exact I.planRight

theorem donor_visible : Finset.univ.image I.placeLeft ∈ (E).scheme.plan :=
  OrderedFaceRestriction.visible I.left (E).scheme I.placeLeft I.imageLeft
    (donor_plan I F hroot hA hB hC hcover)

theorem private_visible : Finset.univ.image I.placeRight ∈ (E).scheme.plan :=
  OrderedFaceRestriction.visible I.right (E).scheme I.placeRight I.imageRight
    (private_plan I F hroot hA hB hC hcover)

theorem restrict_donor :
    (E).restrictFace I.placeLeft (donor_visible I F hroot hA hB hC hcover) = I.left :=
  restrict_eq_of_face I.left (E) I.placeLeft I.imageLeft
    (donor I F hroot hA hB hC hcover) (donor_order I F hroot hA hB hC _ _)
    (donor_plan I F hroot hA hB hC hcover)

theorem restrict_private :
    (E).restrictFace I.placeRight (private_visible I F hroot hA hB hC hcover) = I.right :=
  restrict_eq_of_face I.right (E) I.placeRight I.imageRight
    (privateFace I F hroot hA hB hC hcover) (private_order I F hroot hA hB hC _ _)
    (private_plan I F hroot hA hB hC hcover)

theorem donor_occurrence (d : Cell I.left.scheme) :
    CellScheme.restrictFace.toCell (E).scheme I.placeLeft
      (donor_visible I F hroot hA hB hC hcover)
      (Fin.cast (congrArg (fun D : SemScheme n => D.scheme.card)
        (restrict_donor I F hroot hA hB hC hcover)).symm d) =
      (donor I F hroot hA hB hC hcover).map d :=
  OrderedFaceRestriction.toCell_eq I.left (E).scheme (E).rows I.placeLeft I.imageLeft
    (donor I F hroot hA hB hC hcover) (donor_order I F hroot hA hB hC _ _)
    (donor_plan I F hroot hA hB hC hcover) d

theorem private_occurrence (d : Cell I.right.scheme) :
    CellScheme.restrictFace.toCell (E).scheme I.placeRight
      (private_visible I F hroot hA hB hC hcover)
      (Fin.cast (congrArg (fun D : SemScheme n => D.scheme.card)
        (restrict_private I F hroot hA hB hC hcover)).symm d) =
      (privateFace I F hroot hA hB hC hcover).map d :=
  OrderedFaceRestriction.toCell_eq I.right (E).scheme (E).rows I.placeRight I.imageRight
    (privateFace I F hroot hA hB hC hcover) (private_order I F hroot hA hB hC _ _)
    (private_plan I F hroot hA hB hC hcover) d

end
end LowOnlyPaddedLegal
end VaughtConjecture.Knight
