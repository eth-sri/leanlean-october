/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedLayer
public import VaughtConjecture.Knight.SourceAttachment
public import VaughtConjecture.Knight.RelativeLadderTableDecode
public import VaughtConjecture.Knight.OwnerwiseDecoding
public import VaughtConjecture.Knight.PairedCoupledSections
public import VaughtConjecture.Knight.AmbientGradeCharts
public import VaughtConjecture.Knight.HighLayerBountiful

@[expose] public section

namespace VaughtConjecture.Knight.Padded.Initial

open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} (K : Spec A)

/-- The birth anchor represents ranks of the grade-two source. -/
def baseAnchor (a : K.Anchor 2) : K.Anchor 1 :=
  K.normalize le_rfl (by decide) (K.state a) (K.state_admitted a) (K.state_proper a)

theorem baseAnchor_ranks (a : K.Anchor 2) (d : K.Field) :
    RelativeLadderLayer.ranks (K.fields 1) (baseAnchor K a) d =
      LadderScalarRendering.fieldRank (K.fields 2 a) d := by
  unfold baseAnchor RelativeLadderLayer.ranks
  rw [K.normalize_fields, K.state_profile]
  exact ReceivingCatalogueRanks.fieldRank_normalize 1 _ (K.anchor_proper a) d

theorem field_lawful {j : ℕ} (a : K.Anchor j) :
    RespectsSemanticsBelow K.boundaryRows (A, j) (fun d => K.fields j a (K.field d.1)) := by
  simpa only [K.state_profile] using K.profile_lawful _ (K.state_admitted a)

def predecessor (a : K.Anchor 2) :=
  RelativeLadderLayer.renderWith K.boundary K.one K.field (K.fields 1) (baseAnchor K a)
    (K.fields 2 a) (CanonicalFieldLayer.ceiling 2 K.Field)

/-- At the first added grade all controllers are unweighted. -/
def input : SourceAttachment K.base 2 K.Field (K.Anchor 2) where
  sem := K.baseRows
  pos := by decide
  height := K.height
  separated d hd := by
    have h := K.base_full_grade d ((K.base.scope_subset d).antisymm hd.1)
    exact (by omega : ¬ 2 ≤ K.base.grade d) hd.2
  toAttachmentGrid := AttachmentGrid.canonical 2 (Fintype.card K.Field)
  fields := K.fields 2
  lower := predecessor K
  lower_bound a d _ := RelativeLadderLayer.renderWith_bound K.boundary K.one K.field
    (K.fields 1) _ _ (K.anchor_bound a) d
  lower_lawful a := RelativeLadderLayer.renderWith_respects K.boundary K.boundaryRows K.one
    K.field (K.fields 1) K.proper _ _ (baseAnchor_ranks K a) (K.anchor_bound a)
    (K.anchor_visible (by decide) a) ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (by decide))
    (field_lawful K a)
  lower_prefix a b h hh hag d _ := RelativeLadderLayer.renderWith_agreement
    K.boundary K.one K.field (K.fields 1) (baseAnchor_ranks K a) (baseAnchor_ranks K b)
    (K.anchor_bound a) (K.anchor_bound b) (CanonicalFieldLayer.grid_bound _ _ hh) hag d

local notation "J" => input K

/-- No new cells occur below grade two. -/
def lowerEquiv : K.base.below (A, 1) ≃ (J).carrier.below (A, 1) :=
  SourceLayerCarrier.inheritedEquiv K.base _ 2 (by decide) K.height (A, 1)
    (fun h => by have := h.2; omega)

theorem lower_respects_iff (p : K.base.below (A, 1) → ExtOrd) :
    RespectsSemanticsBelow K.baseRows (A, 1) p ↔
      RespectsSemanticsBelow (J).rows (A, 1) (p ∘ (lowerEquiv K).symm) :=
  respects_iff_of_index_equiv (lowerEquiv K) (SourceLayerCarrier.inheritedEquiv_cell _ _ _ _ _ _ _)
    (fun c d _ => ((J).inherited_row c.1 d).symm) p

theorem source_supported (a : K.Anchor 2) (d : Cell (J).carrier) :
    OrbitPrefixSupport.Supported 2 ((J).grid : Set ExtOrd) (K.fields 2 a) ((J).source a d) := by
  apply (J).source_supported _ a d
  intro b e
  change OrbitPrefixSupport.Supported 2 ((J).grid : Set ExtOrd) (K.fields 2 b)
    (predecessor K b e)
  rcases RelativeLadderLayer.renderWith_supported K.boundary K.one K.field (K.fields 1)
    (baseAnchor K b) (K.fields 2 b) (J).ceiling e with hz | ⟨x, hx⟩ | hc
  · exact Or.inl hz
  · rw [show predecessor K b e = K.fields 2 b x from hx]
    exact OrbitPrefixSupport.supported_field _ _ (K.fields 2 b) x
  · rw [show predecessor K b e = (J).ceiling from hc]
    exact Or.inr (Or.inl (J).ceiling_mem)

theorem source_short (a : K.Anchor 2) (d : Cell (J).carrier) : Short 2 ((J).source a d) :=
  PairedCoupledSections.supported_short (fun _ hz => CanonicalFieldLayer.grid_short _ _ hz)
    (K.anchor_short a) (source_supported K a d)

theorem source_ceiling_at (a : K.Anchor 2) (i : ℕ) (hi : 1 ≤ i) (hi₂ : i ≤ 2) :
    ∃ c, (J).carrier.cell c = (A, i) ∧ (J).source a c = (J).ceiling := by
  have he : i = 1 ∨ i = 2 := by omega
  rcases he with rfl | rfl
  · let v := SupportLadderRows.leaf (H := RelativeLadderLayer.rungs (X := K.Field))
      (X := K.Field) (Nat.succ_pos _) (baseAnchor K a)
    refine ⟨(J).old (RelativeLadderLayer.added K.boundary K.one v),
      ((J).old_index _).trans (RelativeLadderLayer.added_index K.boundary K.one v), ?_⟩
    exact ((J).source_old a _).trans
      (RelativeLadderLayer.renderWith_leaf K.boundary K.one K.field (K.fields 1) _ _ _)
  · exact ⟨_, ((J).controller a).2, (J).data.profile_diagonal _⟩

/-- Install the grade-two leaves, retaining the entire padded predecessor. -/
def layer (hcons : K.boundaryRows.IsConsistent) : Layer K 2 where
  carrier := (J).carrier
  rows := (J).rows
  consistent := (J).consistent (RelativeLadderLayer.consistent K.boundary K.boundaryRows
    K.one K.field (K.fields 1) K.proper hcons (field_lawful K))
  baseMap := (J).old
  base_mono := SourceLayerCarrier.old_order _ _ _ _ _
  base_index := (J).old_index
  base_row := (J).inherited_row
  base_respects := (J).old_respects
  cases d := by
    rcases (J).cell_cases d with h | ⟨a, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨congrArg Prod.fst ((J).controller a).2,
        (congrArg Prod.snd ((J).controller a).2).ge, (congrArg Prod.snd ((J).controller a).2).le⟩
  higher_short := (J).higher_short 2 (source_short K) fun d hs h _ =>
    (Nat.not_succ_le_self 1 (h.trans_eq (K.base_full_grade d hs))).elim
  pos := by decide
  source := (J).source
  controller := (J).controller
  controller_row a := (J).data.row_new ((J).controller a)
  source_leaf := (J).source_new
  baseAnchor := baseAnchor K
  anchor_ranks := baseAnchor_ranks K
  source_base := (J).source_old
  source_chart := fun {_} => (J).exists_chart (K.seed 2 (by decide))
  source_lawful _ := (J).data.profile_respects _
  source_supported := source_supported K
  source_prefix a b _ hh h := (J).source_prefix hh h fun d =>
    RelativeLadderLayer.renderWith_agreement K.boundary K.one K.field (K.fields 1)
      (baseAnchor_ranks K a) (baseAnchor_ranks K b) (K.anchor_bound a) (K.anchor_bound b)
      (CanonicalFieldLayer.grid_bound _ _ hh) h d
  source_ceiling_at := source_ceiling_at K

end

end VaughtConjecture.Knight.Padded.Initial
