
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalRecursiveContract

/-! # Rows of the recursive semantic successor

The predecessor is the actual recursively enlarged lower carrier. Its proved
selected-section operator constructs all new source rows. No future locality
or serving-controller hypothesis is introduced.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows
open    SourcePrefixRows  PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
variable (hp : AvoidsValue D.scope A)
abbrev predecessor := CanonicalRecursiveContract.carrier sem n (Nat.le_of_succ_le hA)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
abbrev Profile := CanonicalRecursiveInventory.Profile sem (n + 4)
local notation "Profile₀" => Profile sem n

local notation "predecessor₀" => predecessor sem n hA

abbrev carrier := SourceLayerCarrier.scheme (predecessor₀) (Profile₀)
  (n + 4) (Nat.succ_pos (n + 3)) hA
local notation "Cell₀" => Cell (predecessor sem n hA)

abbrev old d :=
  SourceLayerCarrier.toCell (predecessor₀) (Profile₀)
    (n + 4) (Nat.succ_pos (n + 3)) hA (.inl d)
abbrev controller := SourceLayerCarrier.controller (predecessor₀) (Profile₀)
  (n + 4) (Nat.succ_pos (n + 3)) hA
include hp in
theorem separation d :
    ¬ GradedLe (A, (n + 4)) ((predecessor₀).cell d) :=
  CanonicalRecursiveInventory.separated sem hp (n + 3) (Nat.le_of_succ_le hA) d
local notation "separation₀" => separation sem n hA hp

abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv (predecessor₀)
  (Profile₀) (n + 4) (Nat.succ_pos (n + 3)) hA (separation₀)
abbrev controllerEquiv := SeparatedSourceLayerCarrier.controllerEquiv (predecessor₀)
  (Profile₀) (n + 4) (Nat.succ_pos (n + 3)) hA (separation₀)
abbrev member := (controllerEquiv sem n hA hp).symm
local notation "member₀" => member sem n hA hp

theorem member_controller (q : Profile₀) :
    member₀ (controller sem n hA q) = q :=
  (controllerEquiv sem n hA hp).symm_apply_apply q
abbrev grid := sourceGrid (n + 4) (Fintype.card (Cell D))
abbrev ceiling := CanonicalFieldLayer.ceiling (n + 4) (Cell D)

local notation "carrier₀" => carrier sem n hA

theorem carrier_eq_recursive :
    carrier₀ = CanonicalRecursiveInventory.scheme sem (n + 4) hA := rfl

theorem profile_lawful (q : Profile₀) :
    RespectsSemanticsBelow sem (A, (n + 4)) (fun d => q.val d.1) := by
  have hr := (GradeCutBoundary.respects_iff sem (A, (n + 4)) le_rfl _).mp
    (q.property.1.toBelow (A, (n + 4)))
  convert hr using 1
  funext d
  exact (congrArg q.val (congrArg Subtype.val
    ((GradeCutBoundary.belowEquiv D (A, (n + 4)) le_rfl).apply_symm_apply d))).symm

def profile_proper (q : Profile₀) d := q.property.2.2 d

local notation "ceiling₀" => ceiling (D := D) n

local notation "grid₀" => grid (D := D) n

local notation "profile_lawful₀" => profile_lawful sem n

local notation "profile_proper₀" => profile_proper sem n

abbrev selected (q : Profile₀) := P.sectionOf (by omega : n + 3 ≤ n + 4)
  (profile_lawful₀ q) (profile_proper₀ q)
  (grid₀) (ceiling₀)

local notation "selected₀" => selected sem n hA P

local notation "selfVis_mono₀" => selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl))

theorem selected_lawful (q : Profile₀) :
    RespectsSemanticsBelow P.rows (A, n + 4)
      (fun d => selected₀ q d.1) :=
  P.section_lawful (by omega) (profile_lawful₀ q) (profile_proper₀ q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
    (selfVis_mono₀ (by omega))

theorem selected_bound (q : Profile₀) (d : Cell₀) :
    selected₀ q d ≤ ceiling₀ :=
  P.section_bound (by omega) (profile_lawful₀ q) (profile_proper₀ q)
    (selfVis_mono₀ (by omega))
    (CanonicalFieldLayer.profile_bound q) d

theorem selected_agreement (p q : Profile₀) {h}
    (hh : h ∈ grid₀) (hag : Agree p.val q.val h) :
    Agree (selected₀ p) (selected₀ q) h :=
  P.section_agreement (by omega) (profile_lawful₀ p) (profile_proper₀ p)
    (profile_lawful₀ q) (profile_proper₀ q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
    (selfVis_mono₀ (by omega))
    hh (CanonicalFieldLayer.grid_bound hh) hag

theorem selected_supported (q : Profile₀) d :
    OrbitPrefixSupport.Supported (n + 4) (grid₀ : Set ExtOrd) q.val
      (selected₀ q d) :=
  P.section_supported (by omega) (profile_lawful₀ q) (profile_proper₀ q)
    (by omega) (sourceGrid_endpoint le_rfl) d

def lower (q : Profile₀) (d : Cell (carrier₀)) :=
  match SourceLayerCarrier.toOcc (predecessor₀) (Profile₀)
      (n + 4) (Nat.succ_pos (n + 3)) hA d with
  | .inl x => selected₀ q x
  | .inr _ => ⊥

local notation "lower₀" => lower sem n hA P

local notation "old₀" => old sem n hA

theorem lower_old (q : Profile₀) (d : Cell₀) :
    lower₀ q (old₀ d) = selected₀ q d := by
  change lower₀ q
    (SourceLayerCarrier.toCell (predecessor₀) (Profile₀)
      (n + 4) (Nat.succ_pos (n + 3)) hA (.inl d)) = _
  simp  [lower, ]

local notation "old_occurrence₀" => SourceLayerCarrier.old_occurrence (predecessor sem n hA) (Profile sem n) (n + 4) (Nat.succ_pos (n + 3)) hA

def data : ScopedSourcePrefixLayer.Data (carrier₀) (n + 4) (Cell D) where
  base := SeparatedSourceLayerCarrier.base (predecessor₀) (Profile₀) (n + 4)
    (Nat.succ_pos (n + 3)) hA separation₀ P.rows
  separated c hc := by
    obtain ⟨x, rfl⟩ := old_occurrence₀ c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact separation₀ x
  grid := grid₀
  bot_mem := sourceGrid_bot
  ceiling := ceiling₀
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (member₀ c).val
  lower c := lower₀ (member₀ c)
  lower_bound c d _ hd := by
    obtain ⟨x, rfl⟩ := old_occurrence₀ d hd
    rw [lower_old]
    exact selected_bound sem n hA P _ x
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := old_occurrence₀ d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff separation₀ P.rows x _).mpr
    change RespectsSemanticsBelow P.rows _
      (fun d => lower₀ _ (old₀ d.1))
    have hx : GradedLe ((predecessor₀).cell x) (A, (n + 4)) :=
      ⟨(predecessor₀).scope_subset x, by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index]
          using hg⟩
    simpa only [lower_old, CellScheme.below.mono] using
      (selected_lawful sem n hA P _).mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := old_occurrence₀ d hd
    simpa only [lower_old] using selected_agreement sem n hA P _ _ hh hag x

local notation "data₀" => data sem n hA hp P

abbrev rows := (data₀).rows
abbrev source (q : Profile₀) := (data₀).profile (controller sem n hA q)
abbrev boundary d :=
  old₀ (CanonicalRecursiveContract.boundary sem n (Nat.le_of_succ_le hA) d)

local notation "source₀" => source sem n hA hp P

theorem source_old (q : Profile₀) (d : Cell₀) :
    source₀ q (old₀ d) = selected₀ q d := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_old _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ (separation₀))]
  change lower₀ (member₀ (controller sem n hA q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary (q : Profile₀) (d : Cell D) :
    source₀ q (boundary sem n hA d) = q.val d := by
  rw [source_old]
  exact P.section_boundary (by omega) (profile_lawful₀ q) (profile_proper₀ q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
    (selfVis_mono₀
      (by omega)) d

theorem source_supported (q : Profile₀) d :
    OrbitPrefixSupport.Supported (n + 4) (grid₀ : Set ExtOrd) q.val
      (source₀ q d) := by
  by_cases hd : (carrier₀).cell d = (A, (n + 4))
  · exact Or.inr (Or.inl (by
      change (data₀).profile _ d ∈ _
      rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ (n + 4)).1 from rfl,
        ScopedSourcePrefixLayer.Data.profile_new]
      exact cut_mem (sourceGrid_bot) _ _))
  · obtain ⟨x, rfl⟩ := old_occurrence₀ d hd
    rw [source_old]
    exact selected_supported sem n hA P q x

def source_short (q : Profile₀) (d : Cell (carrier₀)) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short hh)
    (CanonicalFieldLayer.profile_short q) (source_supported sem n hA hp P q d)

theorem source_agreement_all (p q : Profile₀) {h}
    (hh : h ∈ grid₀) (hag : Agree p.val q.val h) :
    Agree (source₀ p) (source₀ q) h := by
  intro d
  by_cases hd : (carrier₀).cell d = (A, (n + 4))
  · have hb : GradedLe ((carrier₀).cell d) (A, (n + 4)) := by
      rw [hd]; exact GradedLe.refl _
    exact (data₀).profile_prefix hh
      (by simp_all [data, member_controller]) ⟨d, hb⟩
  · obtain ⟨x, rfl⟩ := old_occurrence₀ d hd
    simpa only [source_old] using selected_agreement sem n hA P p q hh hag x

variable {sem n hA hp P} in
theorem inherited_row (c : Cell₀)
    (d : (predecessor₀).belowCell c) :
    (rows sem n hA hp P).E (old₀ c) (ownerEquiv sem n hA hp c d) =
      P.rows.E c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _
    (SeparatedSourceLayerCarrier.old_not_full _ _ (separation₀))]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ d

theorem consistent (hs : sem.IsConsistent) : (rows sem n hA hp P).IsConsistent := by
  apply ScopedSourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := old_occurrence₀ c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff (separation₀) P.rows x _).mpr
  have he : (data₀).base.E (old₀ x) ∘ ownerEquiv sem n hA hp x =
      P.rows.E x := by
    funext d
    exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ d
  rw [he]
  exact P.consistent hs x

