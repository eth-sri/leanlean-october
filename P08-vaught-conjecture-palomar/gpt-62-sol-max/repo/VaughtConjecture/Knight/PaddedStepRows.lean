/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedLayer
public import VaughtConjecture.Knight.ScopedSourcePrefixLayer
public import VaughtConjecture.Knight.PairedCoupledSections
public import VaughtConjecture.Knight.AmbientGradeCharts

public import VaughtConjecture.Knight.SourceAttachment

@[expose] public section

namespace VaughtConjecture.Knight.Padded.StepRows

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition

open PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {K : Spec A} {k : ℕ}
  (P : Layer K k)

local notation "NextAnchor" => K.Anchor (k + 1)

abbrev grid (_P : Layer K k) :=
  sourceGrid (k + 1) (Fintype.card K.Field)

abbrev ceiling (_P : Layer K k) :=
  CanonicalFieldLayer.ceiling (k + 1) K.Field

def selected (a : NextAnchor) : Cell P.carrier → ExtOrd :=
  P.render (Nat.le_succ k) (K.state a) (K.state_admitted a) (K.state_proper a)
    (grid P) (ceiling P)

theorem selected_lawful (a : NextAnchor) :
    RespectsSemanticsBelow P.rows (A, k + 1) (fun d => selected P a d.1) := by
  apply P.lawful (Nat.le_succ k) (K.state a) (K.state_admitted a) (K.state_proper a)
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
  intro d
  rw [K.state_profile]
  exact K.anchor_bound a d

theorem selected_bound (a : NextAnchor) (d : Cell P.carrier) :
    selected P a d ≤ ceiling P := by
  apply P.bound (Nat.le_succ k) (K.state a) (K.state_admitted a) (K.state_proper a)
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
  intro f
  rw [K.state_profile]
  exact K.anchor_bound a f

theorem selected_supported (a : NextAnchor) (d : Cell P.carrier) :
    OrbitPrefixSupport.Supported (k + 1) (grid P : Set ExtOrd) (K.fields (k + 1) a)
      (selected P a d) := by
  simpa only [selected, K.state_profile] using P.supported (Nat.le_succ k) (K.state a)
    (K.state_admitted a) (K.state_proper a) (Nat.le_succ k)
    (G := grid P) (H := ceiling P) (sourceGrid_endpoint le_rfl) d

theorem selected_agreement (a b : NextAnchor) {h : ExtOrd}
    (hh : h ∈ grid P) (hab : Agree (K.fields (k + 1) a) (K.fields (k + 1) b) h) :
    Agree (selected P a) (selected P b) h := by
  apply P.agreement (Nat.le_succ k) (K.state a)
    (K.state_admitted a) (K.state_proper a) (K.state b) (K.state_admitted b) (K.state_proper b)
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    hh (CanonicalFieldLayer.grid_bound _ _ hh)
  simpa [K.state_profile] using hab

variable (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

abbrev carrier := SourceLayerCarrier.scheme P.carrier NextAnchor
  (k + 1) (Nat.succ_pos k) hnext

abbrev old (d : Cell P.carrier) := SourceLayerCarrier.toCell P.carrier NextAnchor
  (k + 1) (Nat.succ_pos k) hnext (.inl d)

abbrev controller := SourceLayerCarrier.controller P.carrier NextAnchor
  (k + 1) (Nat.succ_pos k) hnext

abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv P.carrier NextAnchor
  (k + 1) (Nat.succ_pos k) hnext (P.separated (by omega))

def attachment : SourceAttachment P.carrier (k + 1) K.Field NextAnchor where
  sem := P.rows
  pos := Nat.succ_pos k
  height := hnext
  separated := P.separated (by omega : 1 ≤ k)
  toAttachmentGrid := AttachmentGrid.canonical (k + 1) (Fintype.card K.Field)
  fields := K.fields (k + 1)
  lower := selected P
  lower_bound a d _ := selected_bound P a d
  lower_lawful := selected_lawful P
  lower_prefix a b _ hh hag d _ := selected_agreement P a b hh hag d

abbrev data := (attachment P hk hnext).data

abbrev rows := (data P hk hnext).rows

abbrev source (a : NextAnchor) := (data P hk hnext).profile (controller P hnext a)

theorem source_leaf (a b : NextAnchor) :
    source P hk hnext a (controller P hnext b).1 =
      cut (grid P) (K.fields (k + 1) a) (K.fields (k + 1) b) :=
  (attachment P hk hnext).source_new a b

theorem source_old (a : NextAnchor) (d : Cell P.carrier) :
    source P hk hnext a (old P hnext d) = selected P a d :=
  (attachment P hk hnext).source_old a d

theorem source_lawful (a : NextAnchor) :
    RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)
      (fun d => source P hk hnext a d.1) := (data P hk hnext).profile_respects _

theorem exists_chart {q : (carrier P hnext).below (A, k + 1) → ExtOrd}
    (hq : RespectsSemanticsBelow (rows P hk hnext) (A, k + 1) q) :
    ∃ a : NextAnchor, ∃ σ M, Witness (gTop (k + 1)) σ ∧
      (∀ d, (carrier P hnext).grade d.1 = k + 1 → q d ≤ M) ∧
      ∀ d, σ (source P hk hnext a d.1) = min (q d) M :=
  (attachment P hk hnext).exists_chart (K.seed (k + 1) (Nat.succ_pos k)) hq

theorem source_supported (a : NextAnchor) (d : Cell (carrier P hnext)) :
    OrbitPrefixSupport.Supported (k + 1) (grid P : Set ExtOrd) (K.fields (k + 1) a)
      (source P hk hnext a d) :=
  (attachment P hk hnext).source_supported (selected_supported P) a d

theorem source_short (a : NextAnchor) (d : Cell (carrier P hnext)) :
    Short (k + 1) (source P hk hnext a d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short _ _ hh)
    (K.anchor_short a) (by solve_by_elim [source_supported])

theorem source_agreement (a b : NextAnchor) {h : ExtOrd}
    (hh : h ∈ grid P) (hab : Agree (K.fields (k + 1) a) (K.fields (k + 1) b) h) :
    Agree (source P hk hnext a) (source P hk hnext b) h :=
  (attachment P hk hnext).source_prefix hh hab (selected_agreement P a b hh hab)

theorem inherited_row (c : Cell P.carrier) (d : P.carrier.below (P.carrier.cell c)) :
    (rows P hk hnext).E (old P hnext c) (ownerEquiv P hk hnext c d) = P.rows.E c d :=
  (attachment P hk hnext).inherited_row c d

theorem old_respects (c : Cell P.carrier) (p : Cell (carrier P hnext) → ExtOrd) :
    RespectsSemanticsBelow (rows P hk hnext) ((carrier P hnext).cell (old P hnext c))
      (fun d => p d.1) ↔
      RespectsSemanticsBelow P.rows (P.carrier.cell c) (fun d => p (old P hnext d.1)) :=
  (attachment P hk hnext).old_respects c p

theorem consistent : (rows P hk hnext).IsConsistent :=
  (attachment P hk hnext).consistent P.consistent

end

end VaughtConjecture.Knight.Padded.StepRows
