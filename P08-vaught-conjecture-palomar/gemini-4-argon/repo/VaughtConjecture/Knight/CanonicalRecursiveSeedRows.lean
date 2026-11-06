/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveInventory
public import VaughtConjecture.Knight.CanonicalPairLocalSections

/-! # Actual rows for the recursive third catalogue

This is the semantic bridge from the banked seed pair to the recursive
inventory, including retained higher proper owners. New-controller locality,
availability and consistency are constructed from current-domain sections.
No whole-boundary completion or future-owner lawfulness is assumed.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveSeedRows
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 3 ≤ A.card) (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev two_le := (by decide : 2 ≤ 3).trans hA
abbrev predecessor := CanonicalPairLocalSections.carrier sem (two_le hA)
abbrev predecessorRows := CanonicalPairLocalSections.semantics sem (two_le hA) hp
abbrev Profile := CanonicalRecursiveInventory.Profile sem 3

local notation "pred" => predecessor sem hA
local notation "pRows" => predecessorRows sem hA hp
local notation "Prof" => Profile sem
local notation "pos3" => Nat.succ_pos 2

abbrev carrier := SourceLayerCarrier.scheme pred Prof 3 pos3 hA
abbrev old (d : Cell pred) := SourceLayerCarrier.toCell pred Prof 3 pos3 hA (.inl d)
abbrev controller := SourceLayerCarrier.controller pred Prof 3 pos3 hA

local notation "K" => carrier sem hA
local notation "oldC" => old sem hA
local notation "ctrl" => controller sem hA

include hp in
theorem separation (d : Cell pred) : ¬ GradedLe (A, 3) (CellScheme.cell pred d) :=
  CanonicalRecursiveInventory.separated sem hp 2 (two_le hA) d

local notation "sep" => separation sem hA hp

abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv pred Prof 3 pos3 hA sep
abbrev controllerEquiv := SeparatedSourceLayerCarrier.controllerEquiv pred Prof 3 pos3 hA sep
abbrev member := (controllerEquiv sem hA hp).symm

local notation "oEq" => ownerEquiv sem hA hp
local notation "cEq" => controllerEquiv sem hA hp
local notation "mem" => member sem hA hp

theorem member_controller (q : Prof) : mem (ctrl q) = q := Equiv.symm_apply_apply cEq q

abbrev grid := sourceGrid 3 (Fintype.card (Cell D))
abbrev ceiling := CanonicalFieldLayer.ceiling 3 (Cell D)

local notation "grd" => grid (D := D)
local notation "ceil" => ceiling (D := D)

theorem profile_lawful (q : Prof) :
    RespectsSemanticsBelow sem (A, 3) (fun d => q.val d.1) := by
  convert (GradeCutBoundary.respects_iff D 3 sem (A, 3) le_rfl _).mp
    (q.property.1.toBelow (A, 3)) using 1
  funext d
  exact (congrArg q.val (congrArg Subtype.val
    ((GradeCutBoundary.belowEquiv D 3 (A, 3) le_rfl).apply_symm_apply d))).symm

local notation "pLaw" => profile_lawful sem

abbrev selected (q : Prof) := CanonicalPairLocalSections.sectionOf sem (two_le hA) hp
  (by decide : 2 ≤ 3) (pLaw q) q.2.2.2 grd ceil

local notation "sel" => selected sem hA hp

theorem selected_agreement (p q : Prof) {h : ExtOrd} (hh : h ∈ grd) (hag : Agree p.val q.val h) :
    Agree (sel p) (sel q) h :=
  CanonicalPairLocalSections.section_agreement sem (two_le hA) hp (by decide)
    (pLaw p) p.2.2.2 (pLaw q) q.2.2.2
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by decide))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by decide))
    hh (CanonicalFieldLayer.grid_bound 3 (Cell D) hh) hag

def lower (q : Prof) (d : Cell K) : ExtOrd :=
  match SourceLayerCarrier.toOcc pred Prof 3 pos3 hA d with
  | .inl x => sel q x
  | .inr _ => ⊥

local notation "lwr" => lower sem hA hp

theorem lower_old (q : Prof) (d : Cell pred) : lwr q (oldC d) = sel q d := by
  change lwr q (SourceLayerCarrier.toCell pred Prof 3 pos3 hA (.inl d)) = _
  simp only [lower, SourceLayerCarrier.toOcc_toCell]

def data : ScopedSourcePrefixLayer.Data K 3 (Cell D) where
  base := SeparatedSourceLayerCarrier.base pred Prof 3 pos3 hA sep pRows
  separated c hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof 3 pos3 hA c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact sep x
  grid := grd
  bot_mem := sourceGrid_bot _ _
  ceiling := ceil
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound 3 (Cell D) hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (mem c).val
  lower c := lwr (mem c)
  lower_bound c d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof 3 pos3 hA d hd
    rw [lower_old]
    exact CanonicalPairLocalSections.section_bound sem (two_le hA) hp (by decide)
      (pLaw _) (mem c).2.2.2
      (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by decide))
      (CanonicalFieldLayer.profile_bound (GradeCutBoundary.rows D 3 sem) 3
        (Cell D) (GradeCutBoundary.toCell D 3) _) x
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof 3 pos3 hA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff pred Prof 3 pos3 hA sep pRows x _).mpr
    change RespectsSemanticsBelow pRows _ (fun d => lwr _ (oldC d.1))
    have hx : GradedLe (CellScheme.cell pred x) (A, 3) :=
      ⟨(CellScheme.isPlan pred).subset_of_mem (CellScheme.scope_mem_plan pred x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using hg⟩
    have hl : RespectsSemanticsBelow pRows (A, 3) (fun d => sel (mem c) d.1) :=
      CanonicalPairLocalSections.section_lawful sem (two_le hA) hp (by decide)
        (pLaw _) (mem c).2.2.2
        (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by decide))
        (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by decide))
    simpa only [lower_old, CellScheme.below.mono] using hl.mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof 3 pos3 hA d hd
    simpa only [lower_old] using selected_agreement sem hA hp _ _ hh hag x

local notation "dat" => data sem hA hp

abbrev rows := ScopedSourcePrefixLayer.Data.rows dat
abbrev source (q : Prof) := ScopedSourcePrefixLayer.Data.profile dat (ctrl q)
abbrev boundary (d : Cell D) := oldC (CanonicalPairLocalSections.original sem (two_le hA) d)

local notation "src" => source sem hA hp

theorem source_old (q : Prof) (d : Cell pred) : src q (oldC d) = sel q d := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_old _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ sep d)]
  change lwr (mem (ctrl q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary (q : Prof) (d : Cell D) : src q (boundary sem hA d) = q.val d := by
  rw [source_old]
  exact CanonicalPairLocalSections.section_old sem (two_le hA) hp (by decide) (pLaw q) q.2.2.2 d

theorem source_supported (q : Prof) (d : Cell K) :
    OrbitPrefixSupport.Supported 3 (grd : Set ExtOrd) q.val (src q d) := by
  by_cases hd : CellScheme.cell K d = (A, 3)
  · exact Or.inr (Or.inl (by
      change ScopedSourcePrefixLayer.Data.profile dat _ d ∈ _
      rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ 3).1 from rfl,
        ScopedSourcePrefixLayer.Data.profile_new]
      exact cut_mem (sourceGrid_bot _ _) _ _))
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof 3 pos3 hA d hd
    rw [source_old]
    exact CanonicalPairLocalSections.section_supported sem (two_le hA) hp (by decide)
      (pLaw q) q.2.2.2 (by decide) (sourceGrid_endpoint le_rfl) x

theorem source_short (q : Prof) (d : Cell K) :
    SharpWitnessComposition.Short 3 (src q d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short 3 (Cell D) hh)
    (CanonicalFieldLayer.profile_short (GradeCutBoundary.rows D 3 sem) 3
      (Cell D) (GradeCutBoundary.toCell D 3) q) (source_supported sem hA hp q d)

theorem source_agreement_all (p q : Prof) {h : ExtOrd} (hh : h ∈ grd) (hag : Agree p.val q.val h) :
    Agree (src p) (src q) h := by
  intro d
  by_cases hd : CellScheme.cell K d = (A, 3)
  · exact ScopedSourcePrefixLayer.Data.profile_prefix dat hh
      (by simpa only [data, member_controller] using hag) ⟨d, hd ▸ GradedLe.refl _⟩
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof 3 pos3 hA d hd
    simpa only [source_old] using selected_agreement sem hA hp p q hh hag x

theorem inherited_row (c : Cell pred) (d : CellScheme.below pred (CellScheme.cell pred c)) :
    (rows sem hA hp).E (oldC c) (oEq c d) = Semantics.E pRows c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ sep c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem consistent (hs : sem.IsConsistent) : (rows sem hA hp).IsConsistent := by
  apply ScopedSourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof 3 pos3 hA c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff pred Prof 3 pos3 hA sep pRows x _).mpr
  have he : (ScopedSourcePrefixLayer.Data.base dat).E (oldC x) ∘ oEq x = Semantics.E pRows x :=
    funext fun d => SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ x d
  rw [he]
  exact CanonicalPairBoundary.consistent sem 1 2 (by decide)
    (CanonicalPairLocalSections.one_le (two_le hA)) (by decide) (two_le hA) hp (by decide) hs x
