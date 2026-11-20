/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveContract

public import VaughtConjecture.Knight.SourceAttachment

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows

open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (n : ℕ) (hA : n + 3 ≤ A.card)

variable (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev predecessor := CanonicalRecursiveContract.stageCarrier sem n (Nat.le_of_succ_le hA)

abbrev Profile := CanonicalRecursiveInventory.Profile sem (n + 3)

abbrev carrier := SourceLayerCarrier.scheme (predecessor sem n hA) (Profile sem n)
  (n + 3) (by norm_num) hA

abbrev old (d : Cell (predecessor sem n hA)) :=
  SourceLayerCarrier.toCell (predecessor sem n hA) (Profile sem n)
    (n + 3) (by norm_num) hA (.inl d)

abbrev controller := SourceLayerCarrier.controller (predecessor sem n hA) (Profile sem n)
  (n + 3) (by norm_num) hA

include hp in
theorem separation (d : Cell (predecessor sem n hA)) :
    ¬ GradedLe (A, (n + 3)) ((predecessor sem n hA).cell d) :=
  CanonicalRecursiveInventory.separated sem hp (n + 2) (Nat.le_of_succ_le hA) d

abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv (predecessor sem n hA)
  (Profile sem n) (n + 3) (by norm_num) hA (separation sem n hA hp)

abbrev controllerEquiv := SeparatedSourceLayerCarrier.controllerEquiv (predecessor sem n hA)
  (Profile sem n) (n + 3) (by norm_num) hA (separation sem n hA hp)

abbrev grid := sourceGrid (n + 3) (Fintype.card (Cell D))

abbrev ceiling := CanonicalFieldLayer.ceiling (n + 3) (Cell D)

theorem carrier_eq_recursive :
    carrier sem n hA = CanonicalRecursiveInventory.scheme sem (n + 3) hA := rfl

theorem profile_lawful (q : Profile sem n) :
    RespectsSemanticsBelow sem (A, (n + 3)) (fun d => q.val d.1) := by
  have hr := (GradeCutBoundary.respects_iff D (n + 3) sem (A, (n + 3)) le_rfl _).mp
    (q.property.1.toBelow (A, (n + 3)))
  convert hr using 1
  funext d
  exact (congrArg q.val (congrArg Subtype.val
    ((GradeCutBoundary.belowEquiv D (n + 3) (A, (n + 3)) le_rfl).apply_symm_apply d))).symm

theorem profile_proper (q : Profile sem n) (d : Cell D) : q.val d ≠ ⊤ := q.property.2.2 d

abbrev boundary (d : Cell D) :=
  old sem n hA (CanonicalRecursiveContract.stageBoundary sem n (Nat.le_of_succ_le hA) d)

variable {sem : Semantics D} {n : ℕ} {hA : n + 3 ≤ A.card}
  (S : CanonicalRecursiveContract.Step sem n hA)

abbrev selected (q : Profile sem n) := S.prev.sectionOf (by norm_num)
  (profile_lawful sem n q) (profile_proper sem n q)
  (grid (D := D) n) (ceiling (D := D) n)

theorem selected_lawful (q : Profile sem n) :
    RespectsSemanticsBelow S.prev.rows (A, n + 3)
      (fun d => selected S q d.1) :=
  S.prev.section_lawful (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by norm_num))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by norm_num))

theorem selected_bound (q : Profile sem n) (d : Cell (predecessor sem n hA)) :
    selected S q d ≤ ceiling (D := D) n :=
  S.prev.section_bound (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by norm_num))
    (CanonicalFieldLayer.profile_bound (GradeCutBoundary.rows D (n + 3) sem) (n + 3)
      (Cell D) (GradeCutBoundary.toCell D (n + 3)) q) d

theorem selected_agreement (p q : Profile sem n) {h : ExtOrd}
    (hh : h ∈ grid (D := D) n) (hag : Agree p.val q.val h) :
    Agree (selected S p) (selected S q) h :=
  S.prev.section_agreement (by omega) (profile_lawful sem n p) (profile_proper sem n p)
    (profile_lawful sem n q) (profile_proper sem n q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by norm_num))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by norm_num))
    hh (CanonicalFieldLayer.grid_bound (n + 3) (Cell D) hh) hag

theorem selected_supported (q : Profile sem n) (d : Cell (predecessor sem n hA)) :
    OrbitPrefixSupport.Supported (n + 3) (grid (D := D) n : Set ExtOrd) q.val
      (selected S q d) :=
  S.prev.section_supported (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (by omega) (sourceGrid_endpoint le_rfl) d

def attachment : SourceAttachment (predecessor sem n hA) (n + 3) (Cell D) (Profile sem n) where
  sem := S.prev.rows
  pos := Nat.succ_pos _
  height := hA
  separated := separation sem n hA S.proper
  toAttachmentGrid := AttachmentGrid.canonical (n + 3) (Fintype.card (Cell D))
  fields := Subtype.val
  lower := selected S
  lower_bound q d _ := selected_bound S q d
  lower_lawful := selected_lawful S
  lower_prefix p q _ hh hag d _ := selected_agreement S p q hh hag d

abbrev data := (attachment S).data

abbrev rows := (data S).rows

abbrev source (q : Profile sem n) := (data S).profile (controller sem n hA q)

theorem source_old (q : Profile sem n) (d : Cell (predecessor sem n hA)) :
    source S q (old sem n hA d) = selected S q d :=
  (attachment S).source_old q d

theorem source_boundary (q : Profile sem n) (d : Cell D) :
    source S q (boundary sem n hA d) = q.val d := by
  rw [source_old]
  exact S.prev.section_boundary (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega : n + 2 ≤ n + 3))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl))
      (by omega : n + 2 ≤ n + 3)) d

theorem source_supported (q : Profile sem n) (d : Cell (carrier sem n hA)) :
    OrbitPrefixSupport.Supported (n + 3) (grid (D := D) n : Set ExtOrd) q.val
      (source S q d) :=
  (attachment S).source_supported (selected_supported S) q d

theorem source_short (q : Profile sem n) (d : Cell (carrier sem n hA)) :
    SharpWitnessComposition.Short (n + 3) (source S q d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short (n + 3) (Cell D) hh)
    (CanonicalFieldLayer.profile_short (GradeCutBoundary.rows D (n + 3) sem) (n + 3)
      (Cell D) (GradeCutBoundary.toCell D (n + 3)) q) (by solve_by_elim [source_supported])

theorem source_agreement_all (p q : Profile sem n) {h : ExtOrd}
    (hh : h ∈ grid (D := D) n) (hag : Agree p.val q.val h) :
    Agree (source S p) (source S q) h :=
  (attachment S).source_prefix hh hag (selected_agreement S p q hh hag)

theorem inherited_row (c : Cell (predecessor sem n hA))
    (d : (predecessor sem n hA).below ((predecessor sem n hA).cell c)) :
    (rows S).E (old sem n hA c) (ownerEquiv sem n hA S.proper c d) =
      S.prev.rows.E c d :=
  (attachment S).inherited_row c d

theorem consistent (hs : sem.IsConsistent) : (rows S).IsConsistent :=
  (attachment S).consistent (S.prev.consistent hs)

end

end VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows
