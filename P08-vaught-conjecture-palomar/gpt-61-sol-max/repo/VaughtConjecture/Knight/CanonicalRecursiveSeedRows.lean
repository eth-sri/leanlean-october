
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalRecursiveInventory
import VaughtConjecture.Knight.CanonicalPairLocalSections

/-! # Actual rows for the recursive third catalogue

This is the semantic bridge from the banked seed pair to the recursive
inventory, including retained higher proper owners. New-controller locality,
availability and consistency are constructed from current-domain sections.
No whole-boundary completion or future-owner lawfulness is assumed.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveSeedRows
open    SourcePrefixRows  PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hA : 3 ≤ A.card) (hp : AvoidsValue D.scope A)
abbrev two_le := (by decide : 2 ≤ 3).trans hA
abbrev predecessor := CanonicalPairLocalSections.carrier sem (two_le hA)
abbrev predecessorRows := CanonicalPairLocalSections.semantics sem (two_le hA) hp
abbrev Profile := CanonicalRecursiveInventory.Profile sem 3
local notation "Profile₀" => Profile sem

local notation "predecessor₀" => predecessor sem hA

abbrev carrier := SourceLayerCarrier.scheme (predecessor₀) (Profile₀) 3 (by decide) hA
local notation "Cell₀" => Cell (predecessor sem hA)

abbrev old d :=
  SourceLayerCarrier.toCell (predecessor₀) (Profile₀) 3 (by decide) hA (.inl d)
abbrev controller := SourceLayerCarrier.controller (predecessor₀) (Profile₀)
  3 (by decide) hA
include hp in
theorem separation d :
    ¬ GradedLe (A, 3) ((predecessor₀).cell d) :=
  CanonicalRecursiveInventory.separated sem hp 2 (two_le hA) d
local notation "separation₀" => separation sem hA hp

abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv (predecessor₀)
  (Profile₀) 3 (by decide) hA separation₀
abbrev controllerEquiv := SeparatedSourceLayerCarrier.controllerEquiv (predecessor₀)
  (Profile₀) 3 (by decide) hA separation₀
abbrev member := (controllerEquiv sem hA hp).symm
theorem member_controller q :
    member sem hA hp (controller sem hA q) = q :=
  (controllerEquiv sem hA hp).symm_apply_apply q
abbrev grid := sourceGrid 3 (Fintype.card (Cell D))
abbrev ceiling := CanonicalFieldLayer.ceiling 3 (Cell D)

theorem profile_lawful (q : Profile₀) :
    RespectsSemanticsBelow sem (A, 3) (fun d => q.val d.1) := by
  have hr := (GradeCutBoundary.respects_iff sem (A, 3) le_rfl _).mp
    (q.property.1.toBelow (A, 3))
  convert hr using 1
  funext d
  exact (congrArg q.val (congrArg Subtype.val
    ((GradeCutBoundary.belowEquiv D (A, 3) le_rfl).apply_symm_apply d))).symm

def profile_proper (q : Profile₀) d := q.property.2.2 d

local notation "grid₀" => grid (D := D)

abbrev selected q := CanonicalPairLocalSections.sectionOf sem (two_le hA) hp
  (by decide : 2 ≤ 3) (profile_lawful sem q) (profile_proper sem q)
  (grid₀) (ceiling (D := D))

local notation "predecessorRows₀" => predecessorRows sem hA hp

local notation "selected₀" => selected sem hA hp

local notation "selfVis_mono₀" => selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl))

theorem selected_lawful q :
    RespectsSemanticsBelow (predecessorRows₀) (A, 3)
      (fun d => selected₀ q d.1) :=
  CanonicalPairLocalSections.section_lawful sem (two_le hA) hp (by decide)
    (profile_lawful sem q) (profile_proper sem q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by decide))
    (selfVis_mono₀ (by decide))

theorem selected_bound q d :
    selected₀ q d ≤ ceiling (D := D) :=
  CanonicalPairLocalSections.section_bound sem (two_le hA) hp (by decide)
    (profile_lawful sem q) (profile_proper sem q)
    (selfVis_mono₀ (by decide))
    (CanonicalFieldLayer.profile_bound q) d

theorem selected_agreement (p q : Profile₀) {h}
    (hh : h ∈ grid₀) (hag : Agree p.val q.val h) :
    Agree (selected₀ p) (selected₀ q) h :=
  CanonicalPairLocalSections.section_agreement sem (two_le hA) hp (by decide)
    (profile_lawful sem p) (profile_proper sem p) (profile_lawful sem q) (profile_proper sem q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by decide))
    (selfVis_mono₀ (by decide))
    hh (CanonicalFieldLayer.grid_bound hh) hag

theorem selected_supported (q : Profile₀) d :
    OrbitPrefixSupport.Supported 3 (grid₀ : Set ExtOrd) q.val
      (selected₀ q d) :=
  CanonicalPairLocalSections.section_supported sem (two_le hA) hp (by decide)
    (profile_lawful sem q) (profile_proper sem q) (by decide)
    (sourceGrid_endpoint le_rfl) d

def lower q d :=
  match SourceLayerCarrier.toOcc (predecessor₀) (Profile₀) 3 (by decide) hA d with
  | .inl x => selected₀ q x
  | .inr _ => ⊥

local notation "lower₀" => lower sem hA hp

theorem lower_old q d :
    lower₀ q (old sem hA d) = selected₀ q d := by
  
  simp  [lower, ]

local notation "old_occurrence₀" => SourceLayerCarrier.old_occurrence (predecessor sem hA) (Profile sem) 3

def data : ScopedSourcePrefixLayer.Data (carrier sem hA) 3 (Cell D) where
  base := SeparatedSourceLayerCarrier.base (predecessor₀) (Profile₀) 3
    (by decide) hA separation₀ predecessorRows₀
  separated c hc := by
    obtain ⟨x, rfl⟩ := old_occurrence₀ (by decide) hA c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact separation₀ x
  grid := grid₀
  bot_mem := sourceGrid_bot
  ceiling := ceiling (D := D)
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (member sem hA hp c).val
  lower c := lower₀ (member sem hA hp c)
  lower_bound c d _ hd := by
    obtain ⟨x, rfl⟩ := old_occurrence₀ (by decide) hA d hd
    rw [lower_old]
    exact selected_bound sem hA hp _ x
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := old_occurrence₀ (by decide) hA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff separation₀ predecessorRows₀ x _).mpr
    change RespectsSemanticsBelow predecessorRows₀ _
      (fun d => lower₀ _ (old sem hA d.1))
    have hx : GradedLe ((predecessor₀).cell x) (A, 3) :=
      ⟨(predecessor₀).scope_subset x, by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]
          using hg⟩
    simpa only [lower_old, CellScheme.below.mono] using
      (selected_lawful sem hA hp _).mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := old_occurrence₀ (by decide) hA d hd
    simpa only [lower_old] using selected_agreement sem hA hp _ _ hh hag x

local notation "data₀" => data sem hA hp

abbrev rows := (data₀).rows
abbrev source q := (data₀).profile (controller sem hA q)
abbrev boundary d := old sem hA (CanonicalPairLocalSections.original sem (two_le hA) d)

local notation "source₀" => source sem hA hp

theorem source_old q d :
    source₀ q (old sem hA d) = selected₀ q d := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_old _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ (separation₀))]
  change lower₀ (member sem hA hp (controller sem hA q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary q d :
    source₀ q (boundary sem hA d) = q.val d := by
  rw [source_old]
  exact CanonicalPairLocalSections.section_old d

theorem source_supported (q : Profile₀) d :
    OrbitPrefixSupport.Supported 3 (grid₀ : Set ExtOrd) q.val
      (source₀ q d) := by
  by_cases hd : (carrier sem hA).cell d = (A, 3)
  · exact Or.inr (Or.inl (by
      change (data₀).profile _ d ∈ _
      rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ 3).1 from rfl,
        ScopedSourcePrefixLayer.Data.profile_new]
      exact cut_mem (sourceGrid_bot) _ _))
  · obtain ⟨x, rfl⟩ := old_occurrence₀ (by decide) hA d hd
    rw [source_old]
    exact selected_supported sem hA hp q x

def source_short q d :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short hh)
    (CanonicalFieldLayer.profile_short q) (source_supported sem hA hp q d)

theorem source_agreement_all (p q : Profile₀) {h}
    (hh : h ∈ grid₀) (hag : Agree p.val q.val h) :
    Agree (source₀ p) (source₀ q) h := by
  intro d
  by_cases hd : (carrier sem hA).cell d = (A, 3)
  · have hb : GradedLe ((carrier sem hA).cell d) (A, 3) := by
      rw [hd]; exact GradedLe.refl _
    exact (data₀).profile_prefix hh
      (by simp_all [data, member_controller]) ⟨d, hb⟩
  · obtain ⟨x, rfl⟩ := old_occurrence₀ (by decide) hA d hd
    simpa only [source_old] using selected_agreement sem hA hp p q hh hag x

theorem inherited_row c
    d :
    (rows sem hA hp).E (old sem hA c) (ownerEquiv sem hA hp c d) =
      (predecessorRows₀).E c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _
    (SeparatedSourceLayerCarrier.old_not_full _ _ (separation₀))]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ d

theorem consistent (hs : sem.IsConsistent) : (rows sem hA hp).IsConsistent := by
  apply ScopedSourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := old_occurrence₀ (by decide) hA c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff (separation₀) (predecessorRows₀) x _).mpr
  have he : (data₀).base.E (old sem hA x) ∘ ownerEquiv sem hA hp x =
      (predecessorRows₀).E x := by
    funext d
    exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ d
  rw [he]
  exact CanonicalPairBoundary.consistent hs x

