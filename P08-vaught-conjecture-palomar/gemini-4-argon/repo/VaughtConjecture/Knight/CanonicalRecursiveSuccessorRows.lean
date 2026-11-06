/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveContract

/-! # Rows of the recursive semantic successor

The predecessor is the actual recursively enlarged lower carrier. Its proved
selected-section operator constructs all new source rows. No future locality
or serving-controller hypothesis is introduced.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev predecessor := CanonicalRecursiveContract.carrier sem n (Nat.le_of_succ_le hA)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
abbrev Profile := CanonicalRecursiveInventory.Profile sem (n + 4)

local notation "pred" => predecessor sem n hA
local notation "Prof" => Profile sem n
local notation "pos4" => Nat.succ_pos (n + 3)

abbrev carrier := SourceLayerCarrier.scheme pred Prof (n + 4) pos4 hA
abbrev old (d : Cell pred) := SourceLayerCarrier.toCell pred Prof (n + 4) pos4 hA (.inl d)
abbrev controller := SourceLayerCarrier.controller pred Prof (n + 4) pos4 hA

local notation "K" => carrier sem n hA
local notation "oldC" => old sem n hA
local notation "ctrl" => controller sem n hA

include hp in
theorem separation (d : Cell pred) : ¬ GradedLe (A, n + 4) (CellScheme.cell pred d) :=
  CanonicalRecursiveInventory.separated sem hp (n + 3) (Nat.le_of_succ_le hA) d

local notation "sep" => separation sem n hA hp

abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv pred Prof (n + 4) pos4 hA sep
abbrev controllerEquiv := SeparatedSourceLayerCarrier.controllerEquiv pred Prof (n + 4) pos4 hA sep
abbrev member := (controllerEquiv sem n hA hp).symm

local notation "oEq" => ownerEquiv sem n hA hp
local notation "cEq" => controllerEquiv sem n hA hp
local notation "mem" => member sem n hA hp

theorem member_controller (q : Prof) : mem (ctrl q) = q := Equiv.symm_apply_apply cEq q

abbrev grid := sourceGrid (n + 4) (Fintype.card (Cell D))
abbrev ceiling := CanonicalFieldLayer.ceiling (n + 4) (Cell D)

local notation "grd" => grid (D := D) n
local notation "ceil" => ceiling (D := D) n

theorem profile_lawful (q : Prof) :
    RespectsSemanticsBelow sem (A, n + 4) (fun d => q.val d.1) := by
  convert (GradeCutBoundary.respects_iff D (n + 4) sem (A, n + 4) le_rfl _).mp
    (q.property.1.toBelow (A, n + 4)) using 1
  funext d
  exact (congrArg q.val (congrArg Subtype.val
    ((GradeCutBoundary.belowEquiv D (n + 4) (A, n + 4) le_rfl).apply_symm_apply d))).symm

local notation "pLaw" => profile_lawful sem n

abbrev selected (q : Prof) := P.sectionOf (by omega : n + 3 ≤ n + 4) (pLaw q) q.2.2.2 grd ceil

local notation "sel" => selected sem n hA P

theorem selected_agreement (p q : Prof) {h : ExtOrd} (hh : h ∈ grd) (hag : Agree p.val q.val h) :
    Agree (sel p) (sel q) h :=
  P.section_agreement (by omega) (pLaw p) p.2.2.2 (pLaw q) q.2.2.2
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega))
    hh (CanonicalFieldLayer.grid_bound (n + 4) (Cell D) hh) hag

def lower (q : Prof) (d : Cell K) : ExtOrd :=
  match SourceLayerCarrier.toOcc pred Prof (n + 4) pos4 hA d with
  | .inl x => sel q x
  | .inr _ => ⊥

local notation "lwr" => lower sem n hA P

theorem lower_old (q : Prof) (d : Cell pred) : lwr q (oldC d) = sel q d := by
  change lwr q (SourceLayerCarrier.toCell pred Prof (n + 4) pos4 hA (.inl d)) = _
  simp only [lower, SourceLayerCarrier.toOcc_toCell]

def data : ScopedSourcePrefixLayer.Data K (n + 4) (Cell D) where
  base := SeparatedSourceLayerCarrier.base pred Prof (n + 4) pos4 hA sep P.rows
  separated c hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof (n + 4) pos4 hA c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact sep x
  grid := grd
  bot_mem := sourceGrid_bot _ _
  ceiling := ceil
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound (n + 4) (Cell D) hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := (mem c).val
  lower c := lwr (mem c)
  lower_bound c d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof (n + 4) pos4 hA d hd
    rw [lower_old]
    exact P.section_bound (by omega) (pLaw _) (mem c).2.2.2
      (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega))
      (CanonicalFieldLayer.profile_bound (GradeCutBoundary.rows D (n + 4) sem) (n + 4)
        (Cell D) (GradeCutBoundary.toCell D (n + 4)) _) x
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof (n + 4) pos4 hA d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff pred Prof (n + 4) pos4 hA sep P.rows x _).mpr
    change RespectsSemanticsBelow P.rows _ (fun d => lwr _ (oldC d.1))
    have hx : GradedLe (CellScheme.cell pred x) (A, n + 4) :=
      ⟨(CellScheme.isPlan pred).subset_of_mem (CellScheme.scope_mem_plan pred x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using hg⟩
    have hl : RespectsSemanticsBelow P.rows (A, n + 4) (fun d => sel (mem c) d.1) :=
      P.section_lawful (by omega) (pLaw _) (mem c).2.2.2
        (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
        (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega))
    simpa only [lower_old, CellScheme.below.mono] using hl.mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof (n + 4) pos4 hA d hd
    simpa only [lower_old] using selected_agreement sem n hA P _ _ hh hag x

local notation "dat" => data sem n hA hp P

abbrev rows := ScopedSourcePrefixLayer.Data.rows dat
abbrev source (q : Prof) := ScopedSourcePrefixLayer.Data.profile dat (ctrl q)
abbrev boundary (d : Cell D) := oldC (CanonicalRecursiveContract.boundary sem n (Nat.le_of_succ_le hA) d)

local notation "src" => source sem n hA hp P

theorem source_old (q : Prof) (d : Cell pred) : src q (oldC d) = sel q d := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_old _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ sep d)]
  change lwr (mem (ctrl q)) _ = _
  rw [member_controller, lower_old]

theorem source_boundary (q : Prof) (d : Cell D) : src q (boundary sem n hA d) = q.val d := by
  rw [source_old]
  exact P.section_boundary (by omega) (pLaw q) q.2.2.2
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega)) d

theorem source_supported (q : Prof) (d : Cell K) :
    OrbitPrefixSupport.Supported (n + 4) (grd : Set ExtOrd) q.val (src q d) := by
  by_cases hd : CellScheme.cell K d = (A, n + 4)
  · exact Or.inr (Or.inl (by
      change ScopedSourcePrefixLayer.Data.profile dat _ d ∈ _
      rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ (n + 4)).1 from rfl,
        ScopedSourcePrefixLayer.Data.profile_new]
      exact cut_mem (sourceGrid_bot _ _) _ _))
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof (n + 4) pos4 hA d hd
    rw [source_old]
    exact P.section_supported (by omega) (pLaw q) q.2.2.2 (by omega) (sourceGrid_endpoint le_rfl) x

theorem source_short (q : Prof) (d : Cell K) :
    SharpWitnessComposition.Short (n + 4) (src q d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short (n + 4) (Cell D) hh)
    (CanonicalFieldLayer.profile_short (GradeCutBoundary.rows D (n + 4) sem) (n + 4)
      (Cell D) (GradeCutBoundary.toCell D (n + 4)) q) (source_supported sem n hA hp P q d)

theorem source_agreement_all (p q : Prof) {h : ExtOrd} (hh : h ∈ grd) (hag : Agree p.val q.val h) :
    Agree (src p) (src q) h := by
  intro d
  by_cases hd : CellScheme.cell K d = (A, n + 4)
  · exact ScopedSourcePrefixLayer.Data.profile_prefix dat hh
      (by simpa only [data, member_controller] using hag) ⟨d, hd ▸ GradedLe.refl _⟩
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof (n + 4) pos4 hA d hd
    simpa only [source_old] using selected_agreement sem n hA P p q hh hag x

theorem inherited_row (c : Cell pred) (d : CellScheme.below pred (CellScheme.cell pred c)) :
    (rows sem n hA hp P).E (oldC c) (oEq c d) = P.rows.E c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ sep c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem consistent (hs : sem.IsConsistent) : (rows sem n hA hp P).IsConsistent := by
  apply ScopedSourcePrefixLayer.Data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence pred Prof (n + 4) pos4 hA c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff pred Prof (n + 4) pos4 hA sep P.rows x _).mpr
  have he : (ScopedSourcePrefixLayer.Data.base dat).E (oldC x) ∘ oEq x = P.rows.E x :=
    funext fun d => SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ x d
  rw [he]
  exact P.consistent hs x
