/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedContract

/-! # A higher installed successor over the actual padded LOW predecessor

The predecessor rendering constructs each incoming source. A fresh ceiling
leaf is installed for each member of the next native LOW catalogue. Proper
old owners above that grade and the entire padded base retain their rows.
No ambient lifting or upward admission is used.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedStepRows
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyPaddedContract SourcePrefixRows SharpWitnessComposition PairedSlotComparison

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A} {k : ℕ}
  (P : Layer I F hroot hA hB hC k)

local notation "Anch" => F.Anchor (k + 1)
local notation "Fld" => Field I.left I.right
local notation "kpos" => Nat.succ_pos k

abbrev grid (_P : Layer I F hroot hA hB hC k) := sourceGrid (k + 1) (Fintype.card Fld)
abbrev ceiling (_P : Layer I F hroot hA hB hC k) := CanonicalFieldLayer.ceiling (k + 1) Fld

def selected (a : Anch) : Cell P.carrier → ExtOrd :=
  P.render (Nat.le_succ k) (state F a) (state_admissible F a) (state_proper F a)
    (grid P) (ceiling P)

theorem selected_bound (a : Anch) (d : Cell P.carrier) : selected P a d ≤ ceiling P :=
  P.bound (Nat.le_succ k) (state F a) (state_admissible F a) (state_proper F a)
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by rw [state_profile]; exact LowOnlyRecursiveCharts.anchor_bound F a f) d

theorem selected_agreement (a b : Anch) {h : ExtOrd}
    (hh : h ∈ grid P) (hab : Agree (F.fields (k + 1) a) (F.fields (k + 1) b) h) :
    Agree (selected P a) (selected P b) h :=
  P.agreement (Nat.le_succ k) (state F a) (state F b)
    (state_admissible F a) (state_admissible F b) (state_proper F a) (state_proper F b)
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    hh (CanonicalFieldLayer.grid_bound _ _ hh) (by simpa only [state_profile] using hab)

variable (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)
local notation "hsep" => P.separated I F hroot hA hB hC (by omega)
local notation "old_occ" => SourceLayerCarrier.old_occurrence P.carrier Anch (k + 1) kpos hnext
local notation "base_iff" =>
  SeparatedSourceLayerCarrier.base_respects_iff P.carrier Anch (k + 1) kpos hnext hsep P.rows

abbrev carrier := SourceLayerCarrier.scheme P.carrier Anch (k + 1) kpos hnext
local notation "Car" => carrier P hnext
local notation "Ccell" => CellScheme.cell (carrier P hnext)

abbrev old (d : Cell P.carrier) := SourceLayerCarrier.toCell P.carrier Anch (k + 1) kpos hnext (.inl d)
abbrev controller := SourceLayerCarrier.controller P.carrier Anch (k + 1) kpos hnext
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv P.carrier Anch (k + 1) kpos hnext hsep
abbrev member := (SeparatedSourceLayerCarrier.controllerEquiv P.carrier Anch (k + 1) kpos hnext hsep).symm

theorem member_controller (a : Anch) : member P hk hnext (controller P hnext a) = a :=
  (SeparatedSourceLayerCarrier.controllerEquiv _ _ _ _ _ _).symm_apply_apply a

def lower (a : Anch) (d : Cell Car) : ExtOrd :=
  match SourceLayerCarrier.toOcc P.carrier Anch (k + 1) kpos hnext d with
  | .inl x => selected P a x
  | .inr _ => ⊥

theorem lower_old (a : Anch) (d : Cell P.carrier) :
    lower P hnext a (old P hnext d) = selected P a d := by
  simp only [lower, old, SourceLayerCarrier.toOcc_toCell]

def data : ScopedSourcePrefixLayer.Data Car (k + 1) Fld where
  base := SeparatedSourceLayerCarrier.base P.carrier Anch (k + 1) kpos hnext hsep P.rows
  separated c hc := by
    obtain ⟨d, rfl⟩ := old_occ c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact hsep d
  grid := grid P
  bot_mem := sourceGrid_bot _ _
  ceiling := ceiling P
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound _ _ hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := F.fields (k + 1) (member P hk hnext c)
  lower c := lower P hnext (member P hk hnext c)
  lower_bound c d _ hd := by
    obtain ⟨x, rfl⟩ := old_occ d hd
    rw [lower_old]
    exact selected_bound P _ x
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := old_occ d hd
    apply (base_iff x _).mpr
    have hx : GradedLe (P.carrier.cell x) (A, k + 1) :=
      ⟨P.carrier.isPlan.subset_of_mem (P.carrier.scope_mem_plan x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell,
          SourceLayerCarrier.index] using hg⟩
    have hl : RespectsSemanticsBelow P.rows (A, k + 1) (fun d => selected P _ d.1) :=
      P.lawful (Nat.le_succ k) (state F (member P hk hnext c))
        (state_admissible F _) (state_proper F _)
        (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
        ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
        (fun f => by rw [state_profile]; exact LowOnlyRecursiveCharts.anchor_bound F _ f)
    simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
      lower_old, CellScheme.below.mono] using hl.mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := old_occ d hd
    simpa only [lower_old] using selected_agreement P _ _ hh hag x

abbrev rows := (data P hk hnext).rows
abbrev source (a : Anch) := (data P hk hnext).profile (controller P hnext a)

theorem source_old (a : Anch) (d : Cell P.carrier) :
    source P hk hnext a (old P hnext d) = selected P a d := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_old _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ hsep d)]
  change lower P hnext (member P hk hnext (controller P hnext a)) _ = _
  rw [member_controller, lower_old]

theorem source_new (a b : Anch) :
    source P hk hnext a (controller P hnext b).1 =
      cut (grid P) (F.fields (k + 1) a) (F.fields (k + 1) b) := by
  change (data P hk hnext).profile _ _ = _
  rw [ScopedSourcePrefixLayer.Data.profile_new]
  simp only [data, member_controller]

theorem source_lawful (a : Anch) :
    RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)
      (fun d => source P hk hnext a d.1) := (data P hk hnext).profile_respects _

theorem source_supported (a : Anch) (d : Cell Car) :
    OrbitPrefixSupport.Supported (k + 1) (grid P : Set ExtOrd) (F.fields (k + 1) a)
      (source P hk hnext a d) := by
  by_cases hd : Ccell d = (A, k + 1)
  · change OrbitPrefixSupport.Supported _ _ _ ((data P hk hnext).profile _ d)
    rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ (k + 1)).1 from rfl,
      ScopedSourcePrefixLayer.Data.profile_new]
    exact Or.inr (Or.inl (cut_mem (sourceGrid_bot _ _) _ _))
  · obtain ⟨x, rfl⟩ := old_occ d hd
    rw [source_old]
    simpa only [selected, state_profile] using P.supported (Nat.le_succ k) (state F a)
      (state_admissible F a) (state_proper F a) (Nat.le_succ k)
      (G := grid P) (H := ceiling P) (sourceGrid_endpoint le_rfl) x

theorem source_short (a : Anch) (d : Cell Car) :
    Short (k + 1) (source P hk hnext a d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short _ _ hh)
    (LowOnlyRecursiveCharts.anchor_short F a) (source_supported P hk hnext a d)

theorem source_bound (a : Anch) (d : Cell Car) :
    source P hk hnext a d ≤ ceiling P := by
  by_cases hd : Ccell d = (A, k + 1)
  · exact (data P hk hnext).profile_bound _ d (congrArg Prod.snd hd).le
  · obtain ⟨x, rfl⟩ := old_occ d hd
    rw [source_old]
    exact selected_bound P a x

theorem source_agreement (a b : Anch) {h : ExtOrd}
    (hh : h ∈ grid P) (hab : Agree (F.fields (k + 1) a) (F.fields (k + 1) b) h) :
    Agree (source P hk hnext a) (source P hk hnext b) h := by
  intro d
  by_cases hd : Ccell d = (A, k + 1)
  · exact (data P hk hnext).profile_prefix hh
      (by simpa only [data, member_controller] using hab)
      ⟨d, hd.symm ▸ GradedLe.refl _⟩
  · obtain ⟨x, rfl⟩ := old_occ d hd
    simpa only [source_old] using selected_agreement P a b hh hab x

theorem inherited_row (c : Cell P.carrier) (d : P.carrier.below (P.carrier.cell c)) :
    (rows P hk hnext).E (old P hnext c) (ownerEquiv P hk hnext c d) = P.rows.E c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ hsep c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem old_respects (c : Cell P.carrier) (p : Cell Car → ExtOrd) :
    RespectsSemanticsBelow (rows P hk hnext) (Ccell (old P hnext c))
      (fun d => p d.1) ↔
      RespectsSemanticsBelow P.rows (P.carrier.cell c) (fun d => p (old P hnext d.1)) := by
  rw [(data P hk hnext).old_respects_iff
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ hsep c)]
  exact base_iff c _

theorem consistent : (rows P hk hnext).IsConsistent := by
  apply (data P hk hnext).consistent
  intro c hc
  obtain ⟨x, rfl⟩ := old_occ c hc
  apply (base_iff x _).mpr
  have he : (data P hk hnext).base.E (old P hnext x) ∘ ownerEquiv P hk hnext x = P.rows.E x :=
    funext (SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ x)
  rw [he]
  exact P.consistent x
