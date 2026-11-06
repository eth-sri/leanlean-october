/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyPaddedContract

/-! # A higher installed successor over the actual padded LOW predecessor

The predecessor rendering constructs each incoming source. A fresh ceiling
leaf is installed for each member of the next native LOW catalogue. Proper
old owners above that grade and the entire padded base retain their rows.
No ambient lifting or upward admission is used.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedStepRows
open     LowOnly LowOnlyPaddedContract
open SourcePrefixRows  PairedSlotComparison
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : F.root.Covers I.shared.f I.shared.g}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k)

abbrev grid (_P : Layer I F hroot hA hB hC k) :=
  sourceGrid (k + 1) (Fintype.card (Field I.left I.right))
abbrev ceiling (_P : Layer I F hroot hA hB hC k) :=
  CanonicalFieldLayer.ceiling (k + 1) (Field I.left I.right)

def selected a :=
  P.render (Nat.le_succ k) (state F a) (state_admissible a) (state_proper F a)
    (grid P) (ceiling P)

theorem selected_lawful a :
    RespectsSemanticsBelow P.rows (A, k + 1) (fun d => selected P a d.1) := by
  apply P.lawful (Nat.le_succ k) (state F a) (state_admissible a) (state_proper F a)
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
  intro d
  rw [state_profile]
  exact LowOnlyRecursiveCharts.anchor_bound F a d

theorem selected_bound a d :
    selected P a d ≤ ceiling P := by
  apply P.bound (Nat.le_succ k) (state F a) (state_admissible a) (state_proper F a)
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
  intro f
  rw [state_profile]
  exact LowOnlyRecursiveCharts.anchor_bound F a f

local notation "fields₀" => F.fields (k + 1)

theorem selected_supported a d :
    OrbitPrefixSupport.Supported (k + 1) (grid P : Set ExtOrd) (fields₀ a)
      (selected P a d) := by
  simpa only [selected, state_profile] using P.supported (Nat.le_succ k) (state F a)
    (state_admissible a) (state_proper F a) (Nat.le_succ k)
     (H := ceiling P) (sourceGrid_endpoint le_rfl) d

theorem selected_agreement a b {h}
    (hh : h ∈ grid P) (hab : Agree (fields₀ a) (fields₀ b) h) :
    Agree (selected P a) (selected P b) h := by
  apply P.agreement (Nat.le_succ k) (state F a) (state F b)
    (state_admissible a) (state_admissible b) (state_proper F a) (state_proper F b)
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    hh (CanonicalFieldLayer.grid_bound hh)
  simpa only [state_profile] using hab

variable (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)
abbrev carrier := SourceLayerCarrier.scheme P.carrier (F.Anchor (k + 1))
  (k + 1) (Nat.succ_pos k) hnext
abbrev old d := SourceLayerCarrier.toCell P.carrier (F.Anchor (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (.inl d)
abbrev controller := SourceLayerCarrier.controller P.carrier (F.Anchor (k + 1))
  (k + 1) (Nat.succ_pos k) hnext
local notation "separated₀" => P.separated I F hroot hA hB hC

abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv P.carrier (F.Anchor (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (separated₀ (by omega))
abbrev member := (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (F.Anchor (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (separated₀ (by omega))).symm

theorem member_controller a :
    member P hk hnext (controller P hnext a) = a :=
  (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (F.Anchor (k + 1))
    (k + 1) (Nat.succ_pos k) hnext
    (separated₀ (by omega))).symm_apply_apply a

local notation "Cell₀" => Cell (carrier P hnext)

def lower a d :=
  match SourceLayerCarrier.toOcc P.carrier (F.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d with
  | .inl x => selected P a x
  | .inr _ => ⊥

local notation "old₀" => old P hnext

theorem lower_old a d :
    lower P hnext a (old₀ d) = selected P a d := by
  simp  [lower,  ]

include hk in
theorem old_not_full d :
    (carrier P hnext).cell (old₀ d) ≠ (A, k + 1) :=
  SeparatedSourceLayerCarrier.old_not_full _ _
    (separated₀ (by omega))

local notation "base_respects_iff₀" => SeparatedSourceLayerCarrier.base_respects_iff

local notation "old_occurrence₀" => SourceLayerCarrier.old_occurrence P.carrier (F.Anchor (k + 1)) (k + 1) (Nat.succ_pos k) hnext

def data : ScopedSourcePrefixLayer.Data (carrier P hnext) (k + 1) (Field I.left I.right) where
  base := SeparatedSourceLayerCarrier.base P.carrier (F.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (separated₀ (by omega)) P.rows
  separated c hc := by
    obtain ⟨d, rfl⟩ := old_occurrence₀ c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact separated₀ (by omega) d
  grid := grid P
  bot_mem := sourceGrid_bot
  ceiling := ceiling P
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := fields₀ (member P hk hnext c)
  lower c := lower P hnext (member P hk hnext c)
  lower_bound c d _ hd := by
    obtain ⟨x, rfl⟩ := old_occurrence₀ d hd
    rw [lower_old]
    exact selected_bound P _ x
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := old_occurrence₀ d hd
    apply (base_respects_iff₀ (separated₀ (by omega))
      P.rows x _).mpr
    have hx : GradedLe (P.carrier.cell x) (A, k + 1) :=
      ⟨P.carrier.scope_subset x, by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell,
          SourceLayerCarrier.index] using hg⟩
    simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
      lower_old, CellScheme.below.mono] using (selected_lawful P _).mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := old_occurrence₀ d hd
    simpa only [lower_old] using selected_agreement P _ _ hh hag x

local notation "data₀" => data P hk hnext

abbrev rows := (data₀).rows
abbrev source (a : F.Anchor (k + 1)) := (data₀).profile (controller P hnext a)

local notation "source₀" => source P hk hnext

theorem source_old a d :
    source₀ a (old₀ d) = selected P a d := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_old _ _ (old_not_full P hk hnext d)]
  change lower P hnext (member P hk hnext (controller P hnext a)) _ = _
  rw [member_controller, lower_old]

theorem source_new a b :
    source₀ a (controller P hnext b).1 =
      cut (grid P) (fields₀ a) (fields₀ b) := by
  change (data₀).profile _ _ = _
  rw [ScopedSourcePrefixLayer.Data.profile_new]
  simp  [data, member_controller]

theorem source_lawful a :
    RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)
      (fun d => source₀ a d.1) := (data₀).profile_respects _

theorem source_supported a d :
    OrbitPrefixSupport.Supported (k + 1) (grid P : Set ExtOrd) (fields₀ a)
      (source P hk hnext a d) := by
  by_cases hd : (carrier P hnext).cell d = (A, k + 1)
  · change OrbitPrefixSupport.Supported _ _ _ ((data P hk hnext).profile _ d)
    rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ (k + 1)).1 from rfl,
      ScopedSourcePrefixLayer.Data.profile_new]
    exact Or.inr (Or.inl (cut_mem (sourceGrid_bot) _ _))
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (F.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    rw [source_old]
    exact selected_supported P a x

def source_short a d :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short hh)
    (LowOnlyRecursiveCharts.anchor_short F a) (source_supported P hk hnext a d)

theorem source_bound a d :
    source₀ a d ≤ ceiling P := by
  by_cases hd : (carrier P hnext).cell d = (A, k + 1)
  · exact (data₀).profile_bound _ d (congrArg Prod.snd hd).le
  · obtain ⟨x, rfl⟩ := old_occurrence₀ d hd
    rw [source_old]
    exact selected_bound P a x

theorem source_agreement a b {h}
    (hh : h ∈ grid P) (hab : Agree (fields₀ a) (fields₀ b) h) :
    Agree (source₀ a) (source₀ b) h := by
  intro d
  by_cases hd : (carrier P hnext).cell d = (A, k + 1)
  · exact (data₀).profile_prefix hh
      (by simp_all [data, member_controller])
      ⟨d, hd.symm ▸ GradedLe.refl _⟩
  · obtain ⟨x, rfl⟩ := old_occurrence₀ d hd
    simpa only [source_old] using selected_agreement P a b hh hab x

theorem inherited_row c d :
    (rows P hk hnext).E (old₀ c) (ownerEquiv P hk hnext c d) = P.rows.E c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _ (old_not_full P hk hnext c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ d

theorem old_respects (c : Cell P.carrier) (p : Cell₀ → ExtOrd) :
    RespectsSemanticsBelow (rows P hk hnext) ((carrier P hnext).cell (old₀ c))
      (fun d => p d.1) ↔
      Semantics.RowLawful P.rows c (fun d => p (old₀ d.1)) := by
  rw [(data₀).old_respects_iff (old_not_full P hk hnext c)]
  exact base_respects_iff₀ (separated₀ (by omega)) P.rows c _

theorem consistent : (rows P hk hnext).IsConsistent := by
  apply (data₀).consistent
  intro c hc
  obtain ⟨x, rfl⟩ := old_occurrence₀ c hc
  apply (base_respects_iff₀ (separated₀ (by omega)) P.rows x _).mpr
  have he : (data₀).base.E (old₀ x) ∘ ownerEquiv P hk hnext x = P.rows.E x :=
    funext (SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _)
  rw [he]
  exact P.consistent x

