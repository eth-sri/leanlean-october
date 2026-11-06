
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalPairedProfiles
import VaughtConjecture.Knight.ProperBoundarySourceLayer
import VaughtConjecture.Knight.PairedCoupledSections

/-! # Canonical controllers normalized over the complete field inventory

`X` retains all fields, including fields not yet present at this grade. Both
normalization and controller agreement cuts use all of `X`. Only the actual
occurrence map is projected when checking inherited-row lawfulness. The new
controller family and its selected sections are constructed, not supplied.
-/

namespace VaughtConjecture.Knight.CanonicalFieldLayer
open   ExtOrd SourcePrefixRows SharpWitnessComposition
open PairedSlotEncoding PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (j : ℕ) (X : Type*) [Fintype X] (occ : Cell D → X)

def Profile := {p : X → ExtOrd // RespectsSemantics sem (p ∘ occ) ∧
  p ∈ CanonicalPairedProfiles.inventory X j}

local notation "Profile₀" => Profile sem j X occ

instance : Fintype (Profile₀) :=
  ((CanonicalPairedProfiles.inventory_finite X j).subset (fun _ h => h.2)).fintype

variable {sem j X occ} in
def profile_short (q : Profile₀) x :=
  CanonicalPairedProfiles.inventory_short q.property.2 x

def ceiling := ofOrd (Ordinal.omega0 * (2 * Fintype.card X + 1 : ℕ) + j)

local notation "sourceGrid₀" => sourceGrid j (Fintype.card X)

variable {j X} in
theorem grid_bound {h} (hh : h ∈ sourceGrid₀) :
    h ≤ ceiling j X := by
  classical
  rcases Finset.mem_insert.mp hh with rfl | hh
  · exact bot_le
  · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
    have hb' : b ≤ 2 * Fintype.card X + 1 := by
      grind
    exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)

variable {sem j X occ} in
theorem profile_bound (q : Profile₀) x : q.val x ≤ ceiling j X := by
  apply (CanonicalPairedProfiles.inventory_bound X j q.property.2 x).trans
  exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl)

variable {j X} in
theorem grid_short {h} (hh : h ∈ sourceGrid₀) :
    Short j h := by
  classical
  rcases Finset.mem_insert.mp hh with rfl | hh
  · exact Or.inl rfl
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hh
    exact Or.inr (Or.inr ⟨_, rfl, by rw [finitePart_mul_add]⟩)

variable (hj : 0 < j) (hA : j ≤ A.card)
variable (hproper : AvoidsValue D.scope A)
variable (hg : BoundedBy D.grade j)

variable {sem j X occ} in
def encode {p} (hp : RespectsSemantics sem (p ∘ occ))
    (ht : AvoidsValue p ⊤) : Profile₀ := by
  refine ⟨PairedSlotEncoding.normalize j p, ?_,
    CanonicalPairedProfiles.normalize_mem_inventory X j ht⟩
  have hr := FiniteOrbitEmbedding.map_respects (hp.toBelow (A, j))
    (fun d => hg d.1) (PairedSlotIncoming.encoder_witness j (values p))
    (PairedSlotIncoming.encoder_reflects_bottom j (values p))
  have hw := hr.toRespects
    (fun d => ⟨D.scope_subset d, hg d⟩)
  simpa only [Function.comp_def, PairedSlotIncoming.encoder_profile] using hw

abbrev scheme := SourceLayerCarrier.scheme D (Profile₀) j hj hA
local notation "scheme₀" => scheme sem j X occ hj hA

abbrev old (d : Cell D) : Cell (scheme₀) :=
  SourceLayerCarrier.toCell D (Profile₀) j hj hA (.inl d)
abbrev controller q :=
  SourceLayerCarrier.controller D (Profile₀) j hj hA q
abbrev member := ProperBoundarySourceLayer.member D (Profile₀) j hj hA hproper
abbrev ownerEquiv := ProperBoundarySourceLayer.ownerEquiv D (Profile₀) j hj hA hproper
abbrev lower q :=
  ProperBoundarySourceLayer.lower D (Profile₀) j hj hA (fun q => q.val ∘ occ) q

local notation "lower₀" => lower sem j X occ hj hA

local notation "member₀" => member sem j X occ hj hA hproper

local notation "old₀" => old sem j X occ hj hA

local notation "separated_of_proper₀" => SeparatedSourceLayerCarrier.separated_of_proper D j hproper

def data : SourcePrefixLayer.Data (scheme₀) j X where
  base := ProperBoundarySourceLayer.base D sem Profile₀ j hj hA hproper
  max_grade d := by
    rw [CellScheme.grade, SourceLayerCarrier.cell_eq]
    cases SourceLayerCarrier.toOcc D Profile₀ j hj hA d with
    | inl x => exact hg x
    | inr q => exact le_rfl
  grid := sourceGrid₀
  bot_mem := sourceGrid_bot
  ceiling := ceiling j X
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := grid_bound hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (member₀ c).val
  lower c := lower₀ (member₀ c)
  lower_bound c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D Profile₀ j hj hA d hd
    simpa only [lower, ProperBoundarySourceLayer.lower_old, Function.comp_apply] using
      profile_bound (member₀ c) (occ x)
  lower_lawful c d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D Profile₀ j hj hA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff
      separated_of_proper₀ sem x _).mpr
    change Semantics.RowLawful sem x (fun d =>
      lower₀ (member₀ c)
        (old₀ d.1))
    simpa only [lower, old, ProperBoundarySourceLayer.lower_old] using
      (member₀ c).property.1.toBelow (D.cell x)
  grid_agreement p q h _ hag d hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D Profile₀ j hj hA d hd
    simpa only [lower, old, ProperBoundarySourceLayer.lower_old, Function.comp_apply]
      using hag (occ x)

local notation "data₀" => data sem j X occ hj hA hproper hg

abbrev rows := (data₀).rows
local notation "controller₀" => controller sem j X occ hj hA

abbrev source q :=
  (data₀).profile (controller₀ q)

local notation "source₀" => source sem j X occ hj hA hproper hg

theorem source_old q d :
    source₀ q (old₀ d) = q.val (occ d) := by
  rw [source, SourcePrefixLayer.Data.profile_old _ _ (SeparatedSourceLayerCarrier.old_not_full hj hA
    (separated_of_proper₀))]
  change lower₀
    (member₀ (controller₀ q)) _ = _
  simp  [   ProperBoundarySourceLayer.member_controller,
    ProperBoundarySourceLayer.lower_old, ]

local notation "rows₀" => rows sem j X occ hj hA hproper hg

variable {j X} in
variable {sem occ hj hA hproper hg} in
theorem inherited_row c d :
    (rows₀).E (old₀ c)
      (ownerEquiv sem j X occ hj hA hproper c d) = sem.E c d := by
  rw [SourcePrefixLayer.Data.row_old _ (SeparatedSourceLayerCarrier.old_not_full hj hA
    (separated_of_proper₀))]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ d

theorem consistent (hs : sem.IsConsistent) : (rows₀).IsConsistent := by
  apply SourcePrefixLayer.Data.consistent
  intro d hd
  obtain ⟨c, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile₀) j hj hA d hd
  apply (SeparatedSourceLayerCarrier.base_respects_iff
    (separated_of_proper₀) sem c _).mpr
  have he : (data₀).base.E (old₀ c) ∘
      ownerEquiv sem j X occ hj hA hproper c = sem.E c := by
    funext d
    exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ d
  rw [he]
  exact hs c

theorem source_prefix (p q : Profile₀) {h}
    (hh : h ∈ sourceGrid₀) (hag : Agree p.val q.val h) :
    Agree (source₀ p)
      (source₀ q) h := by
  apply (data₀).profile_prefix hh
  change Agree (member₀ (controller₀ p)).val
    (member₀ (controller₀ q)).val h
  simpa only [  ProperBoundarySourceLayer.member_controller] using hag

variable {sem j X occ hj hA} in
theorem full_source_short c
    (hc : (scheme₀).scope c = A)
    d :
    Short ((scheme₀).grade c) ((rows₀).E c d) := by
  apply (data₀).full_source_short
    (fun _ hh => grid_short hh) _ _ c hc d
  · intro q x hx
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile₀) j hj hA x hx
    change Short j (lower₀ (member₀ q)
      (old₀ y))
    simpa only [ ProperBoundarySourceLayer.lower_old, Function.comp_apply] using
      profile_short (member₀ q) (occ y)
  · intro x hs hx
    obtain ⟨y, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile₀) j hj hA x hx
    exact (hproper y (by grind [CellScheme.scope, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index])).elim

variable {p : X → ExtOrd} (hp : RespectsSemantics sem (p ∘ occ)) (ht : AvoidsValue p ⊤)
variable {G : Finset ExtOrd} {C : ExtOrd}

local notation "encode₀" => encode hg hp ht

def sectionOf G C d :=
  PairedSlotDecoder.decode j (values p) G C
    (source₀ (encode₀) d)

local notation "sectionOf₀" => sectionOf sem j X occ hj hA hproper hg hp ht

theorem section_old (hG : VisibleOn j G) (hC : SelfVis j C) d :
    sectionOf₀ G C (old₀ d) = p (occ d) := by
  rw [sectionOf, source_old]
  exact PairedSlotDecoder.decode_normalize hG hC ht

theorem section_lawful (hG : VisibleOn j G) (hC : SelfVis j C) :
    RespectsSemantics (rows₀)
      (sectionOf₀ G C) := by
  apply (data₀).decoded_respects
    (controller₀ (encode₀)) le_rfl
    (PairedSlotDecoder.decode_witness hG hC) _ (full_source_short hproper hg)
  intro c hc
  have hc' : (scheme₀).cell c ≠ (A, j) := fun he => hc (congrArg Prod.fst he)
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Profile₀) j hj hA c hc'
  apply (SeparatedSourceLayerCarrier.base_respects_iff
    (separated_of_proper₀) sem x _).mpr
  change Semantics.RowLawful sem x (fun d =>
    PairedSlotDecoder.decode j (values p) G C
      (lower₀
        (member₀
          (controller₀ (encode₀)))
        (old₀ d.1)))
  simp  [   ProperBoundarySourceLayer.member_controller,
    ProperBoundarySourceLayer.lower_old, ]
  change Semantics.RowLawful sem x (fun d =>
    PairedSlotDecoder.decode j (values p) G C (PairedSlotEncoding.normalize j p (occ d.1)))
  simpa only [PairedSlotDecoder.decode_normalize hG hC ht, Function.comp_apply] using
    hp.toBelow (D.cell x)

theorem section_bound (hC : SelfVis j C) (hb : BoundedBy p C)
    d :
    sectionOf₀ G C d ≤ C := by
  apply PairedSlotDecoder.decode_le hC
  intro a ha
  obtain ⟨x, hx⟩ := mem_values.mp ha
  simpa only [hx] using hb x

theorem section_supported {K} (hjK : j ≤ K) (hCG : C ∈ G)
    d :
    OrbitPrefixSupport.Supported K (G : Set ExtOrd) p
      (sectionOf₀ G C d) :=
  PairedSlotDecoder.decode_supported hjK hCG _

/-- Both outer decoder parameters are held fixed. Agreement includes all
actual new controller coordinates, not just the projected old fields. -/
theorem section_agreement {q} (hq : RespectsSemantics sem (q ∘ occ))
    (htq : AvoidsValue q ⊤) {h}
    (hG : VisibleOn j G) (hC : SelfVis j C)
    (hh : h ∈ G) (hhC : h ≤ C) (hag : Agree p q h) :
    Agree (sectionOf₀ G C)
      (sectionOf sem j X occ hj hA hproper hg hq htq G C) h := by
  obtain ⟨heG, _, heAgree, hpReach, hqReach, hcompare⟩ :=
    largestCommonCut_spec hG hC hC hh hhC hhC ht htq hag
  have hs := source_prefix sem j X occ hj hA hproper hg
    (encode₀) (encode hg hq htq) heG heAgree
  exact hs.decode (PairedSlotDecoder.decode_witness hG hC).mono
    (PairedSlotDecoder.decode_witness hG hC).mono hpReach hqReach (fun _ _ => hcompare _)

