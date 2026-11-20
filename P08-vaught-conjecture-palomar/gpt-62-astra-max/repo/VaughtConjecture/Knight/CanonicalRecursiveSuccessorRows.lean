/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceFamily
public import VaughtConjecture.Knight.CanonicalRecursiveContract

/-! # Rows of the recursive semantic successor

The predecessor is the actual recursively enlarged lower carrier. Its proved
selected-section operator constructs all new source rows. No future locality
or serving-controller hypothesis is introduced.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows
open Transform Value ExtOrd SourcePrefixRows PairedSlotEncoding PairedSlotComparison
noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 1 ≤ A.card)
variable (hp : D.AvoidsScope A)
abbrev predecessor := CanonicalRecursiveContract.carrier sem n (Nat.le_of_succ_le hA)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
abbrev Profile := CanonicalRecursiveInventory.Profile sem (n + 1)
abbrev carrier := SourceLayerCarrier.scheme (predecessor sem n hA) (Profile sem n)
  (n + 1) (Nat.succ_pos n) hA
abbrev old (d : Cell (predecessor sem n hA)) :=
  SourceLayerCarrier.toCell (predecessor sem n hA) (Profile sem n)
    (n + 1) (Nat.succ_pos n) hA (.inl d)
abbrev controller := SourceLayerCarrier.controller (predecessor sem n hA) (Profile sem n)
  (n + 1) (Nat.succ_pos n) hA
include hp in
theorem separation (d : Cell (predecessor sem n hA)) :
    ¬ GradedLe (A, (n + 1)) ((predecessor sem n hA).cell d) :=
  CanonicalRecursiveInventory.separated sem hp n (Nat.le_of_succ_le hA) d
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv (predecessor sem n hA)
  (Profile sem n) (n + 1) (Nat.succ_pos n) hA (separation sem n hA hp)
abbrev controllerEquiv := SeparatedSourceLayerCarrier.controllerEquiv (predecessor sem n hA)
  (Profile sem n) (n + 1) (Nat.succ_pos n) hA (separation sem n hA hp)
abbrev grid := sourceGrid (n + 1) (Fintype.card (Cell D))
abbrev ceiling := CanonicalFieldLayer.ceiling (n + 1) (Cell D)

theorem carrier_eq_recursive :
    carrier sem n hA = CanonicalRecursiveInventory.scheme sem (n + 1) hA := rfl

theorem profile_lawful (q : Profile sem n) :
    RespectsSemanticsBelow sem (A, (n + 1)) (fun d => q.val d.1) := by
  have hr := (GradeCutBoundary.respects_iff D (n + 1) sem (A, (n + 1)) le_rfl _).mp
    (q.property.1.toBelow (A, (n + 1)))
  convert hr using 1
  funext d
  exact (congrArg q.val (congrArg Subtype.val
    ((GradeCutBoundary.belowEquiv D (n + 1) (A, (n + 1)) le_rfl).apply_symm_apply d))).symm

theorem profile_proper (q : Profile sem n) (d : Cell D) : q.val d ≠ ⊤ := q.property.2.2 d

abbrev selected (q : Profile sem n) := P.sectionOf (by omega : n ≤ n + 1)
  (profile_lawful sem n q) (profile_proper sem n q)
  (grid (D := D) n) (ceiling (D := D) n)

theorem selected_lawful (q : Profile sem n) :
    RespectsSemanticsBelow P.rows (A, n + 1)
      (fun d => selected sem n hA P q d.1) :=
  P.section_lawful (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega : n ≤ n + 1))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega : n ≤ n + 1))

theorem selected_bound (q : Profile sem n) (d : Cell (predecessor sem n hA)) :
    selected sem n hA P q d ≤ ceiling (D := D) n :=
  P.section_bound (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega : n ≤ n + 1))
    (CanonicalFieldLayer.profile_bound (GradeCutBoundary.rows D (n + 1) sem) (n + 1)
      (Cell D) (GradeCutBoundary.toCell D (n + 1)) q) d

theorem selected_agreement (p q : Profile sem n) {h : ExtOrd}
    (hh : h ∈ grid (D := D) n) (hag : Agree p.val q.val h) :
    Agree (selected sem n hA P p) (selected sem n hA P q) h :=
  P.section_agreement (by omega) (profile_lawful sem n p) (profile_proper sem n p)
    (profile_lawful sem n q) (profile_proper sem n q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega : n ≤ n + 1))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl)) (by omega : n ≤ n + 1))
    hh (CanonicalFieldLayer.grid_bound (n + 1) (Cell D) hh) hag

theorem selected_supported (q : Profile sem n) (d : Cell (predecessor sem n hA)) :
    OrbitPrefixSupport.Supported (n + 1) (grid (D := D) n : Set ExtOrd) q.val
      (selected sem n hA P q d) :=
  P.section_supported (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (by omega) (sourceGrid_endpoint le_rfl) d

def family : SourceFamily (predecessor sem n hA) (n + 1) (Cell D) (Profile sem n) where
  sem := P.rows
  positive := Nat.succ_pos _
  height := hA
  separated := separation sem n hA hp
  fields := Subtype.val
  lower := selected sem n hA P
  lower_lawful := selected_lawful sem n hA P
  lower_bound a d _ := selected_bound sem n hA P a d
  lower_prefix a b h hh hf d _ := selected_agreement sem n hA P a b hh hf d
  grid := grid (D := D) n
  bot_mem := sourceGrid_bot _ _
  ceiling := ceiling (D := D) n
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound (n + 1) (Cell D) hh
  grid_visible _ hh := sourceGrid_visible hh

abbrev data := (family sem n hA hp P).data id

abbrev rows := (data sem n hA hp P).rows
abbrev source (q : Profile sem n) := (data sem n hA hp P).profile (controller sem n hA q)
abbrev boundary (d : Cell D) :=
  old sem n hA (CanonicalRecursiveContract.boundary sem n (Nat.le_of_succ_le hA) d)

theorem source_old (q : Profile sem n) (d : Cell (predecessor sem n hA)) :
    source sem n hA hp P q (old sem n hA d) = selected sem n hA P q d :=
  (family sem n hA hp P).source_old q d

theorem source_boundary (q : Profile sem n) (d : Cell D) :
    source sem n hA hp P q (boundary sem n hA d) = q.val d := by
  rw [source_old]
  exact P.section_boundary (by omega) (profile_lawful sem n q) (profile_proper sem n q)
    (fun _ hz => selfVis_mono (sourceGrid_visible hz) (by omega : n ≤ n + 1))
    (selfVis_mono (sourceGrid_visible (sourceGrid_endpoint le_rfl))
      (by omega : n ≤ n + 1)) d

theorem source_supported (q : Profile sem n) (d : Cell (carrier sem n hA)) :
    OrbitPrefixSupport.Supported (n + 1) (grid (D := D) n : Set ExtOrd) q.val (source sem n hA hp P q d) :=
  (family sem n hA hp P).source_supported q (selected_supported sem n hA P q) d

theorem source_short (q : Profile sem n) (d : Cell (carrier sem n hA)) :
    SharpWitnessComposition.Short (n + 1) (source sem n hA hp P q d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short (n + 1) (Cell D) hh)
    (CanonicalFieldLayer.profile_short (GradeCutBoundary.rows D (n + 1) sem) (n + 1)
      (Cell D) (GradeCutBoundary.toCell D (n + 1)) q) (source_supported sem n hA hp P q d)

theorem source_agreement_all (p q : Profile sem n) {h : ExtOrd}
    (hh : h ∈ grid (D := D) n) (hag : Agree p.val q.val h) :
    Agree (source sem n hA hp P p) (source sem n hA hp P q) h :=
  (family sem n hA hp P).source_agrees hh hag (selected_agreement sem n hA P p q hh hag)

theorem inherited_row (c : Cell (predecessor sem n hA))
    (d : (predecessor sem n hA).RowDomain c) :
    (rows sem n hA hp P).E (old sem n hA c) (ownerEquiv sem n hA hp c d) =
      P.rows.E c d :=
  (family sem n hA hp P).inherited_row id c d

theorem consistent (hs : sem.IsConsistent) : (rows sem n hA hp P).IsConsistent :=
  (data sem n hA hp P).consistent ((family sem n hA hp P).base_consistent id (P.consistent hs))

end
end VaughtConjecture.Knight.CanonicalRecursiveSuccessorRows
