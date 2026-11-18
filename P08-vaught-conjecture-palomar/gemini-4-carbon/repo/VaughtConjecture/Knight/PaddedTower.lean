/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RecursiveRungRendering
public import VaughtConjecture.Knight.CanonicalCodingSupport
public import VaughtConjecture.Knight.SeparatedLayerFace
public import VaughtConjecture.Knight.PaddedFaceLift
public import VaughtConjecture.Knight.WholeDonorBoundary

@[expose] public section

namespace VaughtConjecture.Knight.RelativeLadderLayer
open Transform Value ExtOrd
noncomputable section
variable {ι X Q : Type*} [DecidableEq ι] [Fintype X] [Fintype Q] {A : Finset ι}
  (D : CellScheme A) (hA : 0 < A.card) (field : Cell D → X) (fields : Q → X → ExtOrd)

theorem renderWith_decode_normalized (j : ℕ) (a : Q) (p : X → ExtOrd)
    (hp : ∀ x, p x ≠ ⊤) {G : Finset ExtOrd} {H T : ExtOrd}
    (hG : ∀ z ∈ G, SelfVis j z) (hH : SelfVis j H)
    (hT : PairedSlotDecoder.decode j (PairedSlotEncoding.values p) G H T = H)
    (d : Cell (carrier D hA (X := X) (Q := Q))) :
    PairedSlotDecoder.decode j (PairedSlotEncoding.values p) G H
      (renderWith D hA field fields a (PairedSlotEncoding.normalize j p) T d) =
        renderWith D hA field fields a p H d := by
  let f := PairedSlotIncoming.encoder j (PairedSlotEncoding.values p)
  let g := PairedSlotDecoder.decode j (PairedSlotEncoding.values p) G H
  have hf := PairedSlotIncoming.encoder_bounded j (PairedSlotEncoding.values p)
  have hg : Witness (gTop j) g := PairedSlotDecoder.decode_witness hG hH
  have hinv (x : X) : g (f (p x)) = p x := by
    dsimp only [f, g]
    rw [PairedSlotIncoming.encoder_profile]
    exact PairedSlotDecoder.decode_normalize hG hH hp x
  have he := RungTableRendering.level_decode p hf.mono hg.mono hf.bot hg.bot hinv T
    (rankIndex D hA field fields a d)
  simpa only [renderWith, image, f, g, PairedSlotIncoming.encoder_profile, hT] using he

end
end VaughtConjecture.Knight.RelativeLadderLayer

namespace VaughtConjecture.Knight.LadderWeightedSuccessor
open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer
noncomputable section
variable {ι X Q U : Type*} [DecidableEq ι]
  [Fintype X] [Fintype Q] [Fintype U] {A : Finset ι}

structure Input (D : CellScheme A) where
  sem : Semantics D
  proper : ∀ d : Cell D, D.scope d ≠ A
  height : 2 ≤ A.card
  field : Cell D → X
  fields : Q → X → ExtOrd
  birth : ∀ a, RespectsSemanticsBelow sem (A, 1) (fun d => fields a (field d.1))
  anchor : U → Q
  upper : U → X → ExtOrd
  rank_match : ∀ u x, RelativeLadderLayer.ranks fields (anchor u) x =
    LadderScalarRendering.fieldRank (upper u) x
  incoming : ∀ u, RespectsSemanticsBelow sem (A, 2) (fun d => upper u (field d.1))
  visible : ∀ u x, SelfVis 1 (upper u x)
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis 2 h
  bounded : ∀ u x, upper u x ≤ ceiling

namespace Input
variable {D : CellScheme A} (I : Input (X := X) (Q := Q) (U := U) D)

abbrev one : 0 < A.card := lt_of_lt_of_le (by decide : 0 < 2) I.height
abbrev lower := RelativeLadderLayer.carrier D I.one (X := X) (Q := Q)
abbrev lowerRows := RelativeLadderLayer.rows D I.sem I.one I.field I.fields I.proper
abbrev carrier := SourceLayerCarrier.scheme I.lower U 2 (by decide) I.height
abbrev old (d : Cell I.lower) : Cell I.carrier :=
  SourceLayerCarrier.toCell I.lower U 2 (by decide) I.height (.inl d)
abbrev added (u : U) : Cell I.carrier :=
  SourceLayerCarrier.toCell I.lower U 2 (by decide) I.height (.inr u)

omit [Fintype U] in
theorem separation (d : Cell I.lower) : ¬ GradedLe (A, 2) (I.lower.cell d) := by
  rcases RelativeLadderLayer.cell_cases D I.one d with ⟨x, rfl⟩ | ⟨v, rfl⟩
  · rw [RelativeLadderLayer.old_index]
    exact SeparatedSourceLayerCarrier.separated_of_proper D 2 I.proper x
  · rw [RelativeLadderLayer.added_index]
    exact fun h => (by omega : ¬ 2 ≤ 1) h.2

abbrev controller := SeparatedSourceLayerCarrier.controller I.lower U 2 (by decide) I.height
abbrev member := (SeparatedSourceLayerCarrier.controllerEquiv I.lower U 2 (by decide) I.height I.separation).symm
@[simp] theorem member_controller (u : U) : I.member (I.controller u) = u := Equiv.symm_apply_apply _ u

def predecessor (u : U) : Cell I.lower → ExtOrd :=
  RelativeLadderLayer.renderWith D I.one I.field I.fields (I.anchor u) (I.upper u) I.ceiling

omit [Fintype U] in
theorem predecessor_lawful (u : U) : RespectsSemanticsBelow I.lowerRows (A, 2)
    (fun d => I.predecessor u d.1) :=
  RelativeLadderLayer.renderWith_respects D I.sem I.one I.field I.fields I.proper _ _
    (I.rank_match u) (I.bounded u) (I.visible u)
    ((I.grid_visible _ I.ceiling_mem).mono (by decide)) (I.incoming u)

omit [Fintype U] in
theorem predecessor_bound (u : U) (d : Cell I.lower) : I.predecessor u d ≤ I.ceiling :=
  RelativeLadderLayer.renderWith_bound D I.one I.field I.fields _ _ (I.bounded u) d

omit [Fintype U] in
theorem predecessor_prefix (u v : U) {h : ExtOrd} (hh : h ≤ I.ceiling)
    (hag : Agree (I.upper u) (I.upper v) h) (d : Cell I.lower) :
    min (I.predecessor u d) h = min (I.predecessor v d) h :=
  RelativeLadderLayer.renderWith_agreement D I.one I.field I.fields
    (I.rank_match u) (I.rank_match v) (I.bounded u) (I.bounded v) hh hag d

def lowerVector (u : U) (d : Cell I.carrier) : ExtOrd :=
  match SourceLayerCarrier.toOcc I.lower U 2 (by decide) I.height d with
  | .inl x => I.predecessor u x
  | .inr _ => ⊥

theorem lowerVector_old (u : U) (d : Cell I.lower) :
    I.lowerVector u (I.old d) = I.predecessor u d := by
  simp only [lowerVector, old, SourceLayerCarrier.toOcc_toCell]

def data : ScopedSourcePrefixLayer.Data I.carrier 2 X where
  base := SeparatedSourceLayerCarrier.base I.lower U 2 (by decide) I.height I.separation I.lowerRows
  separated c hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower U 2 (by decide) I.height c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact I.separation x
  grid := I.grid
  bot_mem := I.bot_mem
  ceiling := I.ceiling
  ceiling_mem := I.ceiling_mem
  grid_bound := I.grid_bound
  grid_visible := I.grid_visible
  boundary q := I.upper (I.member q)
  lower q := I.lowerVector (I.member q)
  lower_bound q d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower U 2 (by decide) I.height d hd
    rw [lowerVector_old]
    exact I.predecessor_bound _ x
  lower_lawful q c hg hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower U 2 (by decide) I.height c hc
    apply (SeparatedSourceLayerCarrier.base_respects_iff I.lower U 2 (by decide) I.height I.separation I.lowerRows x _).mpr
    change RespectsSemanticsBelow I.lowerRows _ (fun d => I.lowerVector _ (I.old d.1))
    have hx : GradedLe (I.lower.cell x) (A, 2) :=
      ⟨I.lower.isPlan.subset_of_mem (I.lower.scope_mem_plan x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using hg⟩
    simpa only [lowerVector_old, CellScheme.below.mono] using (I.predecessor_lawful _).mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower U 2 (by decide) I.height d hd
    simpa only [lowerVector_old] using I.predecessor_prefix _ _ (I.grid_bound h hh) hag x

abbrev rows := I.data.rows
abbrev source (u : U) := I.data.profile (I.controller u)

theorem source_lawful (u : U) : RespectsSemanticsBelow I.rows (A, 2) (fun d => I.source u d.1) :=
  I.data.profile_respects (I.controller u)

theorem inherited_row (c : Cell I.lower) (d : I.lower.below (I.lower.cell c)) :
    I.rows.E (I.old c) (SeparatedSourceLayerCarrier.ownerEquiv I.lower U
      2 (by decide) I.height I.separation c d) = I.lowerRows.E c d := by
  rw [I.data.row_old (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separation c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ I.separation _ c d

theorem consistent (hs : I.sem.IsConsistent) : I.rows.IsConsistent := by
  apply I.data.consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower U 2 (by decide) I.height c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff I.lower U 2 (by decide) I.height I.separation I.lowerRows x _).mpr
  simpa only [Function.comp_def, data, SeparatedSourceLayerCarrier.base_old] using
    RelativeLadderLayer.consistent D I.sem I.one I.field I.fields I.proper hs I.birth x

theorem source_old (u : U) (d : Cell I.lower) : I.source u (I.old d) = I.predecessor u d := by
  rw [source, I.data.profile_old (I.controller u) (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separation d)]
  change I.lowerVector (I.member (I.controller u)) (I.old d) = _
  rw [member_controller, lowerVector_old]

theorem source_original (u : U) (d : Cell D) :
    I.source u (I.old (RelativeLadderLayer.old D I.one d)) = I.upper u (I.field d) := by
  rw [source_old]
  exact RelativeLadderLayer.renderWith_old D I.one I.field I.fields _ _ _ (I.rank_match u) d

theorem source_parent (u : U) : I.source u (I.added u) = I.ceiling :=
  I.data.profile_diagonal (I.controller u)

omit [Fintype U] in
theorem predecessor_supported (u : U) (d : Cell I.lower) :
    OrbitPrefixSupport.Supported 2 (I.grid : Set ExtOrd) (I.upper u) (I.predecessor u d) := by
  rcases RelativeLadderLayer.renderWith_supported D I.one I.field I.fields
      (I.anchor u) (I.upper u) I.ceiling d with hz | ⟨x, hx⟩ | hc
  · exact Or.inl hz
  · rw [show I.predecessor u d = I.upper u x from hx]
    rcases ExtOrd.cases (I.upper u x) with hb | ht | ⟨v, hv⟩
    · exact Or.inl hb
    · exact Or.inr (Or.inr ⟨x, 2, le_rfl, by rw [ht, extVisibilityReplace_top]⟩)
    · by_cases hi : finitePart v < 2
      · exact Or.inr (Or.inr ⟨x, finitePart v, hi.le, by
          rw [hv, extVisibilityReplace_of_finitePart_lt hi, limitPart_add_finitePart]⟩)
      · exact Or.inr (Or.inr ⟨x, 2, le_rfl, by
          rw [hv, extVisibilityReplace_of_le_finitePart (not_lt.mp hi)]⟩)
  · apply Or.inr; apply Or.inl
    change RelativeLadderLayer.renderWith D I.one I.field I.fields _ _ _ _ ∈ I.grid
    rw [hc]; exact I.ceiling_mem

theorem source_prefix_all (u v : U) {h : ExtOrd} (hh : h ∈ I.grid)
    (hag : Agree (I.upper u) (I.upper v) h) (d : Cell I.carrier) :
    min (I.source u d) h = min (I.source v d) h := by
  by_cases hd : I.carrier.cell d = (A, 2)
  · exact I.data.profile_prefix (p := I.controller u) (q := I.controller v) hh
      (by simpa only [data, member_controller] using hag) ⟨d, hd.symm ▸ GradedLe.refl _⟩
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower U 2 (by decide) I.height d hd
    rw [source_old, source_old]
    exact I.predecessor_prefix u v (I.grid_bound h hh) hag x

theorem source_supported_all (u : U) (d : Cell I.carrier) :
    OrbitPrefixSupport.Supported 2 (I.grid : Set ExtOrd) (I.upper u) (I.source u d) := by
  by_cases hd : I.carrier.cell d = (A, 2)
  · change OrbitPrefixSupport.Supported 2 (I.grid : Set ExtOrd) (I.upper u) (I.data.profile (I.controller u) d)
    rw [show d = (⟨d, hd⟩ : Controller I.carrier 2).1 from rfl, ScopedSourcePrefixLayer.Data.profile_new]
    exact Or.inr (Or.inl (cut_mem I.bot_mem _ _))
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence I.lower U 2 (by decide) I.height d hd
    rw [source_old]
    exact I.predecessor_supported u x

end Input
end
end VaughtConjecture.Knight.LadderWeightedSuccessor

namespace VaughtConjecture.Knight.PaddedTower

open Transform Value ExtOrd AmalgamationPlan CoatomBoundaryExtension
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison PaddedFaceLift

noncomputable section

structure Catalogue.{uS, uQ} {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
    {R : Finset (Finset ι)} {mL mR mJ : ℕ}
    (I : WholeDonorBoundary.Input A B C R mL mR mJ) where
  hA : 2 ≤ A.card
  Fld : Type
  [fintypeFld : Fintype Fld]
  St : Type uS
  profile : St → Fld → ExtOrd
  Admissible : ℕ → St → Prop
  Anchor : ℕ → Type uQ
  [fintypeAnchor : ∀ j, Fintype (Anchor j)]
  fields : ∀ j, Anchor j → Fld → ExtOrd
  anchor_inv : ∀ {j} (a : Anchor j), fields j a ∈ CanonicalPairedProfiles.inventory Fld j
  field : Cell I.boundary → Fld
  proper : ∀ d : Cell I.boundary, I.boundary.scope d ≠ A
  birth_lawful : ∀ a : Anchor 1,
    RespectsSemanticsBelow I.rows (A, 1) (fun d => fields 1 a (field d.1))
  incoming_lawful : ∀ a : Anchor 2,
    RespectsSemanticsBelow I.rows (A, 2) (fun d => fields 2 a (field d.1))
  baseAnchor : Anchor 2 → Anchor 1
  baseAnchor_ranks : ∀ a d,
    RelativeLadderLayer.ranks (fields 1) (baseAnchor a) d =
      LadderScalarRendering.fieldRank (fields 2 a) d
  visible_one : ∀ (a : Anchor 2) d, SelfVis 1 (fields 2 a d)
  anchor_bound : ∀ {j} (a : Anchor j) d, fields j a d ≤ RecursiveRungRendering.ceiling Fld j
  profile_visible_one : ∀ {j}, 1 ≤ j → ∀ {S : St}, Admissible j S → ∀ d, SelfVis 1 (profile S d)
  boundary_lawful_at : ∀ (j : ℕ) (S : St), Admissible j S →
    RespectsSemanticsBelow I.rows (A, j) (fun d => profile S (field d.1))
  normalized : ∀ (k : ℕ), 1 ≤ k → ∀ {j : ℕ}, k ≤ j → ∀ (S : St),
    Admissible j S → (∀ d, profile S d ≠ ⊤) → Anchor k
  normalized_fields : ∀ (k : ℕ) (hk : 1 ≤ k) {j : ℕ} (hj : k ≤ j) (S : St)
    (hS : Admissible j S) (hp : ∀ d, profile S d ≠ ⊤),
    fields k (normalized k hk hj S hS hp) = PairedSlotEncoding.normalize k (profile S)
  state : ∀ {j : ℕ}, Anchor j → St
  state_admissible : ∀ {j : ℕ} (a : Anchor j), Admissible j (state a)
  state_profile : ∀ {j : ℕ} (a : Anchor j), profile (state a) = fields j a
  state_proper : ∀ {j : ℕ} (a : Anchor j) (d : Fld), profile (state a) d ≠ ⊤
  zeroSt : St
  zero_admissible : ∀ t, Admissible (t + 2) zeroSt
  zero_proper : ∀ d, profile zeroSt d ≠ ⊤

attribute [instance] Catalogue.fintypeFld Catalogue.fintypeAnchor

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {mL mR mJ : ℕ}
  {I : WholeDonorBoundary.Input A B C R mL mR mJ}
  (M : Catalogue I)

theorem field_coded {j : ℕ} (a : M.Anchor j) (d : M.Fld) :
    IsCodedLabel j (M.fields j a d) := by
  rcases mem_codedAlphabet_iff.mp (CanonicalPairedProfiles.inventory_coded M.Fld j (M.anchor_inv a) d)
    with hb | ⟨b, i, _, hi, he⟩
  · exact Or.inl hb
  · exact Or.inr ⟨b, i, hi, he⟩

def input : LadderWeightedSuccessor.Input
    (X := M.Fld) (Q := M.Anchor 1) (U := M.Anchor 2) I.boundary where
  sem := I.rows
  proper := M.proper
  height := M.hA
  field := M.field
  fields := M.fields 1
  birth := M.birth_lawful
  anchor := M.baseAnchor
  upper := M.fields 2
  rank_match := M.baseAnchor_ranks
  incoming := M.incoming_lawful
  visible := M.visible_one
  grid := RecursiveRungRendering.grid M.Fld 2
  bot_mem := sourceGrid_bot _ _
  ceiling := RecursiveRungRendering.ceiling M.Fld 2
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hz := CanonicalFieldLayer.grid_bound _ _ hz
  grid_visible _ hz := sourceGrid_visible hz
  bounded := M.anchor_bound

abbrev succCarrier := (input M).carrier
abbrev succRows := (input M).rows
abbrev succSource := (input M).source
abbrev succOld := (input M).old
abbrev succLeaf (a : M.Anchor 2) := (input M).added a
abbrev succOriginal (d : Cell I.boundary) := succOld M
  (RelativeLadderLayer.old I.boundary (Nat.lt_of_lt_of_le (by decide) M.hA) d)

theorem succ_cell_cases (d : Cell (succCarrier M)) :
    (∃ x, d = succOld M x) ∨ ∃ a, d = succLeaf M a := by
  obtain ⟨x, hx⟩ := (SourceLayerCarrier.enumeration (input M).lower
    (M.Anchor 2) 2 (by decide) M.hA).surjective d
  rcases x with x | a
  · exact Or.inl ⟨x, hx.symm⟩
  · exact Or.inr ⟨a, hx.symm⟩

theorem succ_leaf_index (a : M.Anchor 2) :
    (succCarrier M).cell (succLeaf M a) = (A, 2) :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

theorem succ_original_index (d : Cell I.boundary) :
    (succCarrier M).cell (succOriginal M d) = I.boundary.cell d :=
  (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (RelativeLadderLayer.old_index _ _ d)

theorem succ_consistent : (succRows M).IsConsistent :=
  (input M).consistent I.consistent

theorem succ_source_lawful (a : M.Anchor 2) :
    RespectsSemanticsBelow (succRows M) (A, 2) (fun d => succSource M a d.1) :=
  (input M).source_lawful a

theorem succ_inherited_row (c : Cell (input M).lower)
    (d : (input M).lower.below ((input M).lower.cell c)) :
    (succRows M).E (succOld M c)
      (SeparatedSourceLayerCarrier.ownerEquiv (input M).lower
        (M.Anchor 2)
        2 (by decide) M.hA (input M).separation c d) =
      (input M).lowerRows.E c d :=
  (input M).inherited_row c d

theorem succ_original_readback (a : M.Anchor 2) (d : Cell I.boundary) :
    succSource M a (succOriginal M d) = M.fields 2 a (M.field d) :=
  (input M).source_original a d

theorem succ_source_ceiling (a : M.Anchor 2) :
    succSource M a (succLeaf M a) = RecursiveRungRendering.ceiling M.Fld 2 :=
  (input M).source_parent a

theorem succ_source_prefix (a b : M.Anchor 2) {h : ExtOrd}
    (hh : h ∈ RecursiveRungRendering.grid M.Fld 2)
    (hab : Agree (M.fields 2 a) (M.fields 2 b) h) (d : Cell (succCarrier M)) :
    min (succSource M a d) h = min (succSource M b d) h :=
  (input M).source_prefix_all a b hh hab d

theorem succ_source_supported (a : M.Anchor 2) (d : Cell (succCarrier M)) :
    OrbitPrefixSupport.Supported 2 (RecursiveRungRendering.grid M.Fld 2 : Set ExtOrd)
      (M.fields 2 a) (succSource M a d) :=
  (input M).source_supported_all a d

theorem succ_leaf_row (a : M.Anchor 2)
    (d : (succCarrier M).below ((succCarrier M).cell (succLeaf M a))) :
    (succRows M).E (succLeaf M a) d = succSource M a d.1 :=
  (input M).data.row_new ((input M).controller a) d

theorem succ_source_leaf (a b : M.Anchor 2) :
    succSource M a (succLeaf M b) =
      cut (RecursiveRungRendering.grid M.Fld 2) (M.fields 2 a) (M.fields 2 b) := by
  change (input M).data.profile ((input M).controller a) ((input M).controller b).1 = _
  rw [ScopedSourcePrefixLayer.Data.profile_new]
  simp only [LadderWeightedSuccessor.Input.data, LadderWeightedSuccessor.Input.member_controller, input]

theorem succ_source_short (a : M.Anchor 2) (d : Cell (succCarrier M)) :
    Short 2 (succSource M a d) :=
  source_short_of_supported (M.anchor_inv a) (succ_source_supported M a d)

section InitRender
variable {j : ℕ} (hj : 2 ≤ j) (S : M.St) (hS : M.Admissible j S) (hp : ∀ d, M.profile S d ≠ ⊤)
  {G : Finset ExtOrd} {H : ExtOrd}

def anchor2 : M.Anchor 2 := M.normalized 2 (by decide) hj S hS hp

theorem anchor2_ranks (d : M.Fld) :
    RelativeLadderLayer.ranks (M.fields 1) (M.baseAnchor (anchor2 M hj S hS hp)) d =
      LadderScalarRendering.fieldRank (M.profile S) d := by
  rw [M.baseAnchor_ranks, anchor2, M.normalized_fields]
  exact ReceivingCatalogueRanks.fieldRank_normalize 2 (M.profile S) hp d

def initRender (G : Finset ExtOrd) (H : ExtOrd) (d : Cell (succCarrier M)) : ExtOrd :=
  PairedSlotDecoder.decode 2 (PairedSlotEncoding.values (M.profile S)) G H
    (succSource M (anchor2 M hj S hS hp) d)

theorem initRender_old (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hb : ∀ d, M.profile S d ≤ H) (d : Cell (input M).lower) :
    initRender M hj S hS hp G H (succOld M d) =
      RelativeLadderLayer.renderWith I.boundary (input M).one M.field (M.fields 1)
        (M.baseAnchor (anchor2 M hj S hS hp)) (M.profile S) H d := by
  let J := input M
  refine (congrArg (PairedSlotDecoder.decode 2 (PairedSlotEncoding.values (M.profile S)) G H)
    (J.source_old (anchor2 M hj S hS hp) d)).trans ?_
  change PairedSlotDecoder.decode 2 (PairedSlotEncoding.values (M.profile S)) G H
    (RelativeLadderLayer.renderWith I.boundary J.one M.field (M.fields 1)
      (M.baseAnchor _) (M.fields 2 (anchor2 M hj S hS hp)) J.ceiling d) = _
  rw [anchor2, M.normalized_fields]
  exact RelativeLadderLayer.renderWith_decode_normalized I.boundary J.one M.field (M.fields 1)
    2 _ (M.profile S) hp hG hH (decode_reserved_ceiling hH hb) d

theorem initRender_below_old (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hb : ∀ d, M.profile S d ≤ H) (c : Cell (input M).lower)
    (hc : GradedLe ((input M).lower.cell c) (A, j)) :
    RespectsSemanticsBelow (succRows M) ((succCarrier M).cell (succOld M c))
      (fun d => initRender M hj S hS hp G H d.1) := by
  let J := input M
  apply (J.data.old_respects_iff
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ J.separation c)).mpr
  apply (SeparatedSourceLayerCarrier.base_respects_iff J.lower
    (M.Anchor 2)
    2 (by decide) M.hA J.separation J.lowerRows c _).mpr
  have hl : RespectsSemanticsBelow J.lowerRows (J.lower.cell c) _ :=
    (RelativeLadderLayer.renderWith_respects I.boundary I.rows J.one M.field (M.fields 1)
      M.proper _ _ (anchor2_ranks M hj S hS hp) hb (M.profile_visible_one (by have := M.hA; omega) hS)
      (hH.mono (by decide)) (M.boundary_lawful_at j S hS)).mono hc
  simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
    initRender_old M hj S hS hp hG hH hb, CellScheme.below.mono] using hl

theorem initRender_lawful (hG : ∀ z ∈ G, SelfVis 2 z) (hH : SelfVis 2 H)
    (hb : ∀ d, M.profile S d ≤ H) :
    RespectsSemanticsBelow (succRows M) (A, j)
      (fun d => initRender M hj S hS hp G H d.1) := by
  have htwo : RespectsSemanticsBelow (succRows M) (A, 2)
      (fun d => initRender M hj S hS hp G H d.1) := by
    let J := input M
    let a := anchor2 M hj S hS hp
    have hr := succ_source_lawful M a
    have hν := PairedSlotDecoder.decode_witness (S := PairedSlotEncoding.values (M.profile S)) hG hH
    apply map_respects_of_short_or_local hr (fun d => d.2.2) hν
    intro ⟨c, hc⟩
    rcases succ_cell_cases M c with ⟨x, rfl⟩ | ⟨b, rfl⟩
    · right
      have hg : J.lower.grade x ≤ 2 := by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using hc.2
      exact (initRender_below_old M hj S hS hp hG hH hb x
        ⟨J.lower.isPlan.subset_of_mem (J.lower.scope_mem_plan x), hg.trans hj⟩).locality
        ⟨succOld M x, GradedLe.refl _⟩
    · left
      intro d
      simpa only [CellScheme.grade, succ_leaf_index, succ_leaf_row] using
        succ_source_short M b d.1
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro ⟨c, hc⟩
  rcases succ_cell_cases M c with ⟨x, rfl⟩ | ⟨a, ha⟩
  · exact initRender_below_old M hj S hS hp hG hH hb x
      (by simpa only [SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using hc)
  · exact GradeCutLayerRows.cast_respects _ _
      ((congrArg (succCarrier M).cell ha).trans (succ_leaf_index M a)).symm htwo

end InitRender

abbrev base := (input M).lower
abbrev baseRows := (input M).lowerRows

theorem base_full_grade (c : Cell (base M)) (hc : (base M).scope c = A) :
    (base M).grade c = 1 := by
  rcases RelativeLadderLayer.cell_cases I.boundary (Nat.lt_of_lt_of_le (by decide) M.hA) c with ⟨d, rfl⟩ | ⟨v, rfl⟩
  · exact False.elim (M.proper d
      ((congrArg Prod.fst (RelativeLadderLayer.old_index I.boundary (by have := M.hA; omega) d)).symm.trans hc))
  · exact congrArg Prod.snd (RelativeLadderLayer.added_index I.boundary (by have := M.hA; omega) v)

structure Layer (k : ℕ) where
  carrier : CellScheme A
  rows : Semantics carrier
  consistent : rows.IsConsistent
  baseMap : Cell (base M) → Cell carrier
  base_mono : StrictMono baseMap
  base_index : ∀ c, carrier.cell (baseMap c) = (base M).cell c
  base_row : ∀ c (d : (base M).below ((base M).cell c)),
    rows.E (baseMap c) ⟨baseMap d.1, by simpa only [base_index] using d.2⟩ =
      (baseRows M).E c d
  base_respects : ∀ c (p : Cell carrier → ExtOrd),
    RespectsSemanticsBelow rows (carrier.cell (baseMap c)) (fun d => p d.1) ↔
      RespectsSemanticsBelow (baseRows M) ((base M).cell c) (fun d => p (baseMap d.1))
  cases : ∀ d, (∃ c, d = baseMap c) ∨
    carrier.scope d = A ∧ 2 ≤ carrier.grade d ∧ carrier.grade d ≤ k
  higher_short : ∀ c, carrier.scope c = A → 2 ≤ carrier.grade c →
    ∀ d : carrier.below (carrier.cell c), Short (carrier.grade c) (rows.E c d)
  render : ∀ {j : ℕ}, k ≤ j → ∀ S : M.St,
    M.Admissible j S → (∀ d, M.profile S d ≠ ⊤) →
    Finset ExtOrd → ExtOrd → Cell carrier → ExtOrd
  birth : ∀ {j : ℕ} (_hj : k ≤ j) (S : M.St)
    (_hS : M.Admissible j S) (_hp : ∀ d, M.profile S d ≠ ⊤), M.Anchor 1
  birth_ranks : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) d,
    RelativeLadderLayer.ranks (M.fields 1) (birth hj S hS hp) d =
      LadderScalarRendering.fieldRank (M.profile S) d
  render_base : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → (∀ d, M.profile S d ≤ H) → ∀ d,
    render hj S hS hp G H (baseMap d) =
      RelativeLadderLayer.renderWith I.boundary (Nat.lt_of_lt_of_le (by decide) M.hA)
        M.field (M.fields 1) (birth hj S hS hp) (M.profile S) H d
  lawful : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → (∀ d, M.profile S d ≤ H) →
      RespectsSemanticsBelow rows (A, j) (fun d => render hj S hS hp G H d.1)
  bound : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    SelfVis k H → (∀ d, M.profile S d ≤ H) → ∀ d, render hj S hS hp G H d ≤ H
  supported : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G : Finset ExtOrd} {H : ExtOrd} {l : ℕ},
    k ≤ l → H ∈ G → ∀ d,
    OrbitPrefixSupport.Supported l (G : Set ExtOrd) (M.profile S) (render hj S hS hp G H d)
  agreement : ∀ {j} (hj : k ≤ j) (S T) (hS) (hT) (hp) (ht) {G H h},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → h ∈ G → h ≤ H →
    Agree (M.profile S) (M.profile T) h → Agree (render hj S hS hp G H) (render hj T hT ht G H) h
  ceiling_at : ∀ {j} (hj : k ≤ j) (S) (hS) (hp) {G H},
    (∀ z ∈ G, SelfVis k z) → SelfVis k H → (∀ d, M.profile S d ≤ H) →
    ∀ i, 1 ≤ i → i ≤ k → ∃ c, carrier.cell c = (A, i) ∧ render hj S hS hp G H c = H

namespace Layer
variable {M} {k : ℕ} (P : Layer M k)

theorem full_grade (hk : 1 ≤ k) (d : Cell P.carrier) (hd : P.carrier.scope d = A) :
    P.carrier.grade d ≤ k := by
  rcases P.cases d with ⟨c, rfl⟩ | ⟨_, _, hg⟩
  · exact (congrArg Prod.snd (P.base_index c)).le.trans
      ((base_full_grade M c ((congrArg Prod.fst (P.base_index c)).symm.trans hd)).le.trans hk)
  · exact hg

theorem separated (hk : 1 ≤ k) (d : Cell P.carrier) :
    ¬ GradedLe (A, k + 1) (P.carrier.cell d) := fun hd => by
  have hs := Finset.Subset.antisymm
    (P.carrier.isPlan.subset_of_mem (P.carrier.scope_mem_plan d)) hd.1
  have := P.full_grade hk d hs
  have : k + 1 ≤ P.carrier.grade d := hd.2
  omega

theorem original_readback {j : ℕ} (hj : k ≤ j) (S : M.St)
    (hS : M.Admissible j S) (hp : ∀ d, M.profile S d ≠ ⊤) {G H}
    (hG : ∀ z ∈ G, SelfVis k z) (hH : SelfVis k H) (hb : ∀ d, M.profile S d ≤ H)
    (d : Cell I.boundary) :
    P.render hj S hS hp G H (P.baseMap (RelativeLadderLayer.old I.boundary (by have := M.hA; omega) d)) =
      M.profile S (M.field d) :=
  (P.render_base hj S hS hp hG hH hb _).trans
    (RelativeLadderLayer.renderWith_old I.boundary (by have := M.hA; omega) M.field (M.fields 1)
      _ _ _ (P.birth_ranks hj S hS hp) d)
end Layer

def initial : Layer M 2 where
  carrier := succCarrier M
  rows := succRows M
  consistent := succ_consistent M
  baseMap := succOld M
  base_mono := SourceLayerCarrier.old_order _ _ _ _ _
  base_index _ := SourceLayerCarrier.cell_toCell _ _ _ _ _ _
  base_row := succ_inherited_row M
  base_respects c p := by
    let J := input M
    rw [J.data.old_respects_iff
      (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ J.separation c)]
    exact SeparatedSourceLayerCarrier.base_respects_iff J.lower
      (M.Anchor 2)
      2 (by decide) M.hA J.separation J.lowerRows c _
  cases d := by
    rcases succ_cell_cases M d with h | ⟨a, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨congrArg Prod.fst (succ_leaf_index M a),
        (congrArg Prod.snd (succ_leaf_index M a)).ge,
        (congrArg Prod.snd (succ_leaf_index M a)).le⟩
  higher_short c hc hg d := by
    rcases succ_cell_cases M c with ⟨b, rfl⟩ | ⟨a, rfl⟩
    · have hi := SourceLayerCarrier.cell_toCell (base M)
        (M.Anchor 2)
        2 (by decide) M.hA (.inl b)
      have he : (succCarrier M).grade (succOld M b) = 1 :=
        (congrArg Prod.snd hi).trans (base_full_grade M b ((congrArg Prod.fst hi).symm.trans hc))
      omega
    · simpa only [CellScheme.grade, succ_leaf_index, succ_leaf_row] using succ_source_short M a d.1
  render {j} hj S hS hp G H := initRender M hj S hS hp G H
  birth {j} hj S hS hp := M.baseAnchor (anchor2 M hj S hS hp)
  birth_ranks {j} hj S hS hp := anchor2_ranks M hj S hS hp
  render_base {j} hj S hS hp {_ _} := initRender_old M hj S hS hp
  lawful {j} hj S hS hp {_ _} := initRender_lawful M hj S hS hp
  bound {_} _ S _ _ {_ _} hH hb _ := PairedSlotDecoder.decode_le hH (fun _ hv => by
    obtain ⟨x, hx⟩ := PairedSlotEncoding.mem_values.mp hv; simpa only [← hx] using hb x) _
  supported {_} _ _ _ _ {_ _ _} hl hH _ := PairedSlotDecoder.decode_supported hl hH _
  agreement {j} hj S T hS hT hp ht {G H h} hG hH hh hhH hag := by
    obtain ⟨e, heG, he, hpe, hqe, hcompare⟩ := exists_common_cut hG hH hH hh hhH hhH hp ht hag
    have he' : Agree (M.fields 2 (anchor2 M hj S hS hp)) (M.fields 2 (anchor2 M hj T hT ht)) e := by
      rw [anchor2, anchor2, M.normalized_fields, M.normalized_fields]; exact he
    exact Agree.decode (succ_source_prefix M _ _ heG he')
      (PairedSlotDecoder.decode_witness hG hH).mono (PairedSlotDecoder.decode_witness hG hH).mono
      hpe hqe (fun _ _ => hcompare _)
  ceiling_at {j} hj S hS hp {G H} hG hH hb i hi hik := by
    rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl
    · let J := input M
      let a := M.baseAnchor (anchor2 M hj S hS hp)
      let v := SupportLadderRows.leaf (X := M.Fld) (H := RelativeLadderLayer.rungs (X := M.Fld))
        (by unfold RelativeLadderLayer.rungs; omega) a
      let c := RelativeLadderLayer.added I.boundary J.one v
      refine ⟨succOld M c, (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans
        (RelativeLadderLayer.added_index I.boundary J.one v), ?_⟩
      rw [initRender_old M hj S hS hp hG hH hb]
      change LadderScalarRendering.level (LadderScalarRendering.values (M.profile S)) H
        (RelativeLadderLayer.rankIndex I.boundary J.one M.field (M.fields 1) a c) = H
      rw [RelativeLadderLayer.rankIndex_added, SupportLadderRows.index_leaf,
        FiniteProfileControllers.cut_refl]
      exact ite_eq_left (by
        have := LadderScalarRendering.values_card_le (M.profile S)
        unfold RelativeLadderLayer.rungs; omega)
    · refine ⟨succLeaf M (anchor2 M hj S hS hp), succ_leaf_index M _, ?_⟩
      unfold initRender; rw [succ_source_ceiling]; exact decode_reserved_ceiling hH hb

section Step
variable {M} {k : ℕ} (P : Layer M k)

abbrev stepGrid (_P : Layer M k) := sourceGrid (k + 1) (Fintype.card M.Fld)
abbrev stepCeiling (_P : Layer M k) := CanonicalFieldLayer.ceiling (k + 1) M.Fld

def selected (a : M.Anchor (k + 1)) : Cell P.carrier → ExtOrd :=
  P.render (Nat.le_succ k) (M.state a) (M.state_admissible a) (M.state_proper a)
    (stepGrid P) (stepCeiling P)

theorem selected_lawful (a : M.Anchor (k + 1)) :
    RespectsSemanticsBelow P.rows (A, k + 1) (fun d => selected P a d.1) :=
  P.lawful (Nat.le_succ k) (M.state a) (M.state_admissible a) (M.state_proper a)
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    fun d => by rw [M.state_profile]; exact M.anchor_bound a d

theorem selected_bound (a : M.Anchor (k + 1)) (d : Cell P.carrier) :
    selected P a d ≤ stepCeiling P :=
  P.bound (Nat.le_succ k) (M.state a) (M.state_admissible a) (M.state_proper a)
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by rw [M.state_profile]; exact M.anchor_bound a f) d

theorem selected_supported (a : M.Anchor (k + 1)) (d : Cell P.carrier) :
    OrbitPrefixSupport.Supported (k + 1) (stepGrid P : Set ExtOrd) (M.fields (k + 1) a)
      (selected P a d) := by
  simpa only [selected, M.state_profile] using P.supported (Nat.le_succ k) (M.state a)
    (M.state_admissible a) (M.state_proper a) (Nat.le_succ k)
    (G := stepGrid P) (H := stepCeiling P) (sourceGrid_endpoint le_rfl) d

theorem selected_agreement (a b : M.Anchor (k + 1)) {h : ExtOrd}
    (hh : h ∈ stepGrid P) (hab : Agree (M.fields (k + 1) a) (M.fields (k + 1) b) h) :
    Agree (selected P a) (selected P b) h :=
  P.agreement (Nat.le_succ k) (M.state a) (M.state b)
    (M.state_admissible a) (M.state_admissible b) (M.state_proper a) (M.state_proper b)
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    hh (CanonicalFieldLayer.grid_bound _ _ hh) (by simpa only [M.state_profile] using hab)

variable (hk : 2 ≤ k) (hnext : k + 1 ≤ A.card)

abbrev stepCarrier := SourceLayerCarrier.scheme P.carrier (M.Anchor (k + 1))
  (k + 1) (Nat.succ_pos k) hnext
abbrev stepOld (d : Cell P.carrier) := SourceLayerCarrier.toCell P.carrier (M.Anchor (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (.inl d)
abbrev stepController := SourceLayerCarrier.controller P.carrier (M.Anchor (k + 1))
  (k + 1) (Nat.succ_pos k) hnext
abbrev stepOwnerEquiv := SeparatedSourceLayerCarrier.ownerEquiv P.carrier (M.Anchor (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (P.separated (by have := M.hA; omega))
abbrev stepMember := (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (M.Anchor (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (P.separated (by have := M.hA; omega))).symm

theorem step_member_controller (a : M.Anchor (k + 1)) :
    stepMember P hk hnext (stepController P hnext a) = a :=
  (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (M.Anchor (k + 1))
    (k + 1) (Nat.succ_pos k) hnext (P.separated (by have := M.hA; omega))).symm_apply_apply a

def stepLower (a : M.Anchor (k + 1)) (d : Cell (stepCarrier P hnext)) : ExtOrd :=
  match SourceLayerCarrier.toOcc P.carrier (M.Anchor (k + 1)) (k + 1) (Nat.succ_pos k) hnext d with
  | .inl x => selected P a x
  | .inr _ => ⊥

theorem step_lower_old (a : M.Anchor (k + 1)) (d : Cell P.carrier) :
    stepLower P hnext a (stepOld P hnext d) = selected P a d := by
  simp only [stepLower, stepOld, SourceLayerCarrier.toOcc_toCell]

include hk in
theorem step_old_not_full (d : Cell P.carrier) :
    (stepCarrier P hnext).cell (stepOld P hnext d) ≠ (A, k + 1) :=
  SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ (P.separated (by have := M.hA; omega)) d

def stepData : ScopedSourcePrefixLayer.Data (stepCarrier P hnext) (k + 1) M.Fld where
  base := SeparatedSourceLayerCarrier.base P.carrier (M.Anchor (k + 1)) (k + 1)
    (Nat.succ_pos k) hnext (P.separated (by have := M.hA; omega)) P.rows
  separated c hc := by
    obtain ⟨d, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (M.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext c hc
    rw [SourceLayerCarrier.cell_toCell]; exact P.separated (by have := M.hA; omega) d
  grid := stepGrid P
  bot_mem := sourceGrid_bot _ _
  ceiling := stepCeiling P
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound _ _ hh
  grid_visible _ hh := sourceGrid_visible hh
  boundary c := M.fields (k + 1) (stepMember P hk hnext c)
  lower c := stepLower P hnext (stepMember P hk hnext c)
  lower_bound c d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (M.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    rw [step_lower_old]; exact selected_bound P _ x
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (M.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    apply (SeparatedSourceLayerCarrier.base_respects_iff P.carrier (M.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext (P.separated (by have := M.hA; omega)) P.rows x _).mpr
    have hx : GradedLe (P.carrier.cell x) (A, k + 1) :=
      ⟨P.carrier.isPlan.subset_of_mem (P.carrier.scope_mem_plan x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell, SourceLayerCarrier.index] using hg⟩
    simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
      step_lower_old, CellScheme.below.mono] using (selected_lawful P _).mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (M.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    simpa only [step_lower_old] using selected_agreement P _ _ hh hag x

abbrev stepRows := (stepData P hk hnext).rows
abbrev stepSource (a : M.Anchor (k + 1)) := (stepData P hk hnext).profile (stepController P hnext a)

theorem step_source_old (a : M.Anchor (k + 1)) (d : Cell P.carrier) :
    stepSource P hk hnext a (stepOld P hnext d) = selected P a d := by
  rw [stepSource, ScopedSourcePrefixLayer.Data.profile_old _ _ (step_old_not_full P hk hnext d)]
  change stepLower P hnext (stepMember P hk hnext (stepController P hnext a)) _ = _
  rw [step_member_controller, step_lower_old]

theorem step_source_new (a b : M.Anchor (k + 1)) :
    stepSource P hk hnext a (stepController P hnext b).1 =
      cut (stepGrid P) (M.fields (k + 1) a) (M.fields (k + 1) b) := by
  change (stepData P hk hnext).profile _ _ = _
  rw [ScopedSourcePrefixLayer.Data.profile_new]
  simp only [stepData, step_member_controller]

theorem step_source_lawful (a : M.Anchor (k + 1)) :
    RespectsSemanticsBelow (stepRows P hk hnext) (A, k + 1)
      (fun d => stepSource P hk hnext a d.1) := (stepData P hk hnext).profile_respects _

theorem step_source_supported (a : M.Anchor (k + 1)) (d : Cell (stepCarrier P hnext)) :
    OrbitPrefixSupport.Supported (k + 1) (stepGrid P : Set ExtOrd) (M.fields (k + 1) a)
      (stepSource P hk hnext a d) := by
  by_cases hd : (stepCarrier P hnext).cell d = (A, k + 1)
  · change OrbitPrefixSupport.Supported _ _ _ ((stepData P hk hnext).profile _ d)
    rw [show d = (⟨d, hd⟩ : SourcePrefixLayer.Controller _ (k + 1)).1 from rfl,
      ScopedSourcePrefixLayer.Data.profile_new]
    exact Or.inr (Or.inl (cut_mem (sourceGrid_bot _ _) _ _))
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (M.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    rw [step_source_old]; exact selected_supported P a x

theorem step_source_short (a : M.Anchor (k + 1)) (d : Cell (stepCarrier P hnext)) :
    Short (k + 1) (stepSource P hk hnext a d) :=
  source_short_of_supported (M.anchor_inv a) (step_source_supported P hk hnext a d)

theorem step_source_agreement (a b : M.Anchor (k + 1)) {h : ExtOrd}
    (hh : h ∈ stepGrid P) (hab : Agree (M.fields (k + 1) a) (M.fields (k + 1) b) h) :
    Agree (stepSource P hk hnext a) (stepSource P hk hnext b) h := fun d => by
  by_cases hd : (stepCarrier P hnext).cell d = (A, k + 1)
  · exact (stepData P hk hnext).profile_prefix hh
      (by simpa only [stepData, step_member_controller] using hab) ⟨d, hd.symm ▸ GradedLe.refl _⟩
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (M.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    simpa only [step_source_old] using selected_agreement P a b hh hab x

theorem step_inherited_row (c : Cell P.carrier) (d : P.carrier.below (P.carrier.cell c)) :
    (stepRows P hk hnext).E (stepOld P hnext c) (stepOwnerEquiv P hk hnext c d) = P.rows.E c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _ (step_old_not_full P hk hnext c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

theorem step_old_respects (c : Cell P.carrier) (p : Cell (stepCarrier P hnext) → ExtOrd) :
    RespectsSemanticsBelow (stepRows P hk hnext) ((stepCarrier P hnext).cell (stepOld P hnext c))
      (fun d => p d.1) ↔
      RespectsSemanticsBelow P.rows (P.carrier.cell c) (fun d => p (stepOld P hnext d.1)) := by
  rw [(stepData P hk hnext).old_respects_iff (step_old_not_full P hk hnext c)]
  exact SeparatedSourceLayerCarrier.base_respects_iff P.carrier (M.Anchor (k + 1))
    (k + 1) (Nat.succ_pos k) hnext (P.separated (by have := M.hA; omega)) P.rows c _

theorem step_consistent : (stepRows P hk hnext).IsConsistent := by
  apply (stepData P hk hnext).consistent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (M.Anchor (k + 1))
    (k + 1) (Nat.succ_pos k) hnext c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff P.carrier (M.Anchor (k + 1))
    (k + 1) (Nat.succ_pos k) hnext (P.separated (by have := M.hA; omega)) P.rows x _).mpr
  have he : (stepData P hk hnext).base.E (stepOld P hnext x) ∘ stepOwnerEquiv P hk hnext x =
      P.rows.E x := funext (SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ x)
  rw [he]; exact P.consistent x

abbrev stepBaseMap (d : Cell (base M)) := stepOld P hnext (P.baseMap d)

theorem step_base_index (d : Cell (base M)) :
    (stepCarrier P hnext).cell (stepBaseMap P hnext d) = (base M).cell d :=
  (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (P.base_index d)

theorem step_base_row (c : Cell (base M)) (d : (base M).below ((base M).cell c)) :
    (stepRows P hk hnext).E (stepBaseMap P hnext c)
      ⟨stepBaseMap P hnext d.1, by simpa only [step_base_index] using d.2⟩ =
        (baseRows M).E c d :=
  (step_inherited_row P hk hnext (P.baseMap c)
    ⟨P.baseMap d.1, by simpa only [P.base_index] using d.2⟩).trans (P.base_row c d)

theorem step_base_respects (c : Cell (base M)) (p : Cell (stepCarrier P hnext) → ExtOrd) :
    RespectsSemanticsBelow (stepRows P hk hnext) ((stepCarrier P hnext).cell (stepBaseMap P hnext c))
      (fun d => p d.1) ↔
      RespectsSemanticsBelow (baseRows M) ((base M).cell c)
        (fun d => p (stepBaseMap P hnext d.1)) :=
  (step_old_respects P hk hnext (P.baseMap c) p).trans
    (P.base_respects c (fun d => p (stepOld P hnext d)))

include hk in
theorem step_cell_cases (d : Cell (stepCarrier P hnext)) :
    (∃ c, d = stepBaseMap P hnext c) ∨
      (stepCarrier P hnext).scope d = A ∧ 2 ≤ (stepCarrier P hnext).grade d ∧
        (stepCarrier P hnext).grade d ≤ k + 1 := by
  obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration P.carrier (M.Anchor (k + 1))
    (k + 1) (Nat.succ_pos k) hnext).surjective d
  rcases x with x | a
  · rcases P.cases x with ⟨c, rfl⟩ | ⟨hs, hl, hu⟩
    · exact Or.inl ⟨c, rfl⟩
    · have he := SourceLayerCarrier.cell_toCell P.carrier (M.Anchor (k + 1))
        (k + 1) (Nat.succ_pos k) hnext (.inl x)
      exact Or.inr ⟨(congrArg Prod.fst he).trans hs,
        hl.trans_eq (congrArg Prod.snd he).symm,
        (congrArg Prod.snd he).le.trans (hu.trans (Nat.le_succ k))⟩
  · have he := SourceLayerCarrier.cell_toCell P.carrier (M.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext (.inr a)
    exact Or.inr ⟨congrArg Prod.fst he,
      (show 2 ≤ k + 1 by omega).trans_eq (congrArg Prod.snd he).symm, (congrArg Prod.snd he).le⟩

theorem step_higher_short (c : Cell (stepCarrier P hnext)) (hc : (stepCarrier P hnext).scope c = A)
    (hg : 2 ≤ (stepCarrier P hnext).grade c)
    (d : (stepCarrier P hnext).below ((stepCarrier P hnext).cell c)) :
    Short ((stepCarrier P hnext).grade c) ((stepRows P hk hnext).E c d) := by
  by_cases he : (stepCarrier P hnext).cell c = (A, k + 1)
  · let a := stepMember P hk hnext ⟨c, he⟩
    have ha : stepController P hnext a = ⟨c, he⟩ :=
      (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (M.Anchor (k + 1))
        (k + 1) (Nat.succ_pos k) hnext (P.separated (by have := M.hA; omega))).apply_symm_apply _
    rw [(stepData P hk hnext).row_new ⟨c, he⟩ d, show (stepCarrier P hnext).grade c = k + 1 from congrArg Prod.snd he]
    simpa only [stepSource, ha] using step_source_short P hk hnext a d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (M.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext c he
    obtain ⟨e, rfl⟩ := (stepOwnerEquiv P hk hnext x).surjective d
    rw [step_inherited_row]
    have hi := SourceLayerCarrier.cell_toCell P.carrier (M.Anchor (k + 1))
      (k + 1) (Nat.succ_pos k) hnext (.inl x)
    change Short ((stepCarrier P hnext).grade (stepOld P hnext x)) _
    rw [show (stepCarrier P hnext).grade (stepOld P hnext x) = P.carrier.grade x from congrArg Prod.snd hi]
    exact P.higher_short x ((congrArg Prod.fst hi).symm.trans hc) (hg.trans_eq (congrArg Prod.snd hi)) e

def stepNormalized {j : ℕ} (hj : k + 1 ≤ j) (S : M.St)
    (hS : M.Admissible j S) (hp : ∀ d, M.profile S d ≠ ⊤) : M.Anchor (k + 1) :=
  M.normalized (k + 1) (Nat.succ_pos k) hj S hS hp

def stepBirth {j : ℕ} (hj : k + 1 ≤ j) (S : M.St)
    (hS : M.Admissible j S) (hp : ∀ d, M.profile S d ≠ ⊤) : M.Anchor 1 :=
  P.birth (Nat.le_succ k) (M.state (stepNormalized (M := M) hj S hS hp))
    (M.state_admissible _) (M.state_proper _)

theorem step_birth_ranks {j : ℕ} (hj : k + 1 ≤ j) (S : M.St)
    (hS : M.Admissible j S) (hp : ∀ d, M.profile S d ≠ ⊤) (d : M.Fld) :
    RelativeLadderLayer.ranks (M.fields 1) (stepBirth P hj S hS hp) d =
      LadderScalarRendering.fieldRank (M.profile S) d := by
  rw [stepBirth, P.birth_ranks, M.state_profile, stepNormalized, M.normalized_fields]
  exact ReceivingCatalogueRanks.fieldRank_normalize (k + 1) (M.profile S) hp d

def stepRender {j : ℕ} (hj : k + 1 ≤ j) (S : M.St)
    (hS : M.Admissible j S) (hp : ∀ d, M.profile S d ≠ ⊤)
    (G : Finset ExtOrd) (H : ExtOrd) (d : Cell (stepCarrier P hnext)) : ExtOrd :=
  PairedSlotDecoder.decode (k + 1) (PairedSlotEncoding.values (M.profile S)) G H
    (stepSource P hk hnext (stepNormalized hj S hS hp) d)

theorem step_render_base {j : ℕ} (hj : k + 1 ≤ j) (S : M.St)
    (hS : M.Admissible j S) (hp : ∀ d, M.profile S d ≠ ⊤) {G H}
    (hG : ∀ z ∈ G, SelfVis (k + 1) z) (hH : SelfVis (k + 1) H)
    (hb : ∀ d, M.profile S d ≤ H) (d : Cell (base M)) :
    stepRender P hk hnext hj S hS hp G H (stepBaseMap P hnext d) =
      RelativeLadderLayer.renderWith I.boundary (Nat.lt_of_lt_of_le (by decide) M.hA)
        M.field (M.fields 1) (stepBirth P hj S hS hp) (M.profile S) H d := by
  unfold stepRender stepBaseMap
  rw [step_source_old]
  unfold selected
  have he := P.render_base (Nat.le_succ k) (M.state (stepNormalized hj S hS hp))
    (M.state_admissible _) (M.state_proper _) (G := stepGrid P) (H := stepCeiling P)
    (fun _ hz => (sourceGrid_visible hz).mono (Nat.le_succ k))
    ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
    (fun f => by rw [M.state_profile]; exact M.anchor_bound _ f) d
  refine (congrArg (PairedSlotDecoder.decode (k + 1)
    (PairedSlotEncoding.values (M.profile S)) G H) he).trans ?_
  change PairedSlotDecoder.decode (k + 1) (PairedSlotEncoding.values (M.profile S)) G H
    (RelativeLadderLayer.renderWith I.boundary (by have := M.hA; omega) M.field (M.fields 1)
      (stepBirth P hj S hS hp) (M.profile (M.state (stepNormalized hj S hS hp))) (stepCeiling P) d) = _
  rw [M.state_profile, stepNormalized, M.normalized_fields]
  exact RelativeLadderLayer.renderWith_decode_normalized I.boundary (by have := M.hA; omega)
    M.field (M.fields 1) (k + 1) _ (M.profile S) hp hG hH (decode_reserved_ceiling hH hb) d

theorem step_render_base_lawful {j : ℕ} (hj : k + 1 ≤ j) (S : M.St)
    (hS : M.Admissible j S) (hp : ∀ d, M.profile S d ≠ ⊤) {G H}
    (hG : ∀ z ∈ G, SelfVis (k + 1) z) (hH : SelfVis (k + 1) H)
    (hb : ∀ d, M.profile S d ≤ H) (c : Cell (base M)) (hc : (base M).grade c ≤ j) :
    RespectsSemanticsBelow (stepRows P hk hnext) ((stepCarrier P hnext).cell (stepBaseMap P hnext c))
      (fun d => stepRender P hk hnext hj S hS hp G H d.1) := by
  apply (step_base_respects P hk hnext c _).mpr
  simp only [step_render_base P hk hnext hj S hS hp hG hH hb]
  exact (RelativeLadderLayer.renderWith_respects I.boundary I.rows (Nat.lt_of_lt_of_le (by decide) M.hA)
    M.field (M.fields 1) M.proper (stepBirth P hj S hS hp) (M.profile S)
    (step_birth_ranks P hj S hS hp) hb (M.profile_visible_one (by have := M.hA; omega) hS)
    (hH.mono (Nat.succ_pos k)) (M.boundary_lawful_at j S hS)).mono
    ⟨(base M).isPlan.subset_of_mem ((base M).scope_mem_plan c), hc⟩

theorem step_render_lawful {j : ℕ} (hj : k + 1 ≤ j) (S : M.St)
    (hS : M.Admissible j S) (hp : ∀ d, M.profile S d ≠ ⊤) {G H}
    (hG : ∀ z ∈ G, SelfVis (k + 1) z) (hH : SelfVis (k + 1) H)
    (hb : ∀ d, M.profile S d ≤ H) :
    RespectsSemanticsBelow (stepRows P hk hnext) (A, j)
      (fun d => stepRender P hk hnext hj S hS hp G H d.1) := by
  have hnat : RespectsSemanticsBelow (stepRows P hk hnext) (A, k + 1)
      (fun d => stepRender P hk hnext hj S hS hp G H d.1) := by
    apply map_respects_of_short_or_local
      (step_source_lawful P hk hnext (stepNormalized hj S hS hp)) (fun d => d.2.2)
      (PairedSlotDecoder.decode_witness (S := PairedSlotEncoding.values (M.profile S)) hG hH)
    intro ⟨c, hc⟩
    rcases step_cell_cases P hk hnext c with ⟨b, rfl⟩ | ⟨hs, hl, _⟩
    · right
      have hb' : (base M).grade b ≤ j := by
        simpa only [CellScheme.grade, step_base_index] using hc.2.trans hj
      exact (step_render_base_lawful P hk hnext hj S hS hp hG hH hb b hb').locality
        ⟨stepBaseMap P hnext b, GradedLe.refl _⟩
    · exact Or.inl (step_higher_short P hk hnext c hs hl)
  apply ScopedSourcePrefixLayer.respects_below_of_lower
  intro ⟨c, hc⟩
  rcases step_cell_cases P hk hnext c with ⟨b, rfl⟩ | ⟨_, _, hu⟩
  · exact step_render_base_lawful P hk hnext hj S hS hp hG hH hb b
      (by simpa only [CellScheme.grade, step_base_index] using hc.2)
  · exact hnat.mono ⟨(stepCarrier P hnext).isPlan.subset_of_mem
      ((stepCarrier P hnext).scope_mem_plan c), hu⟩

def successor : Layer M (k + 1) where
  carrier := stepCarrier P hnext
  rows := stepRows P hk hnext
  consistent := step_consistent P hk hnext
  baseMap := stepBaseMap P hnext
  base_mono := (SourceLayerCarrier.old_order _ _ _ _ _).comp P.base_mono
  base_index := step_base_index P hnext
  base_row := step_base_row P hk hnext
  base_respects := step_base_respects P hk hnext
  cases := step_cell_cases P hk hnext
  higher_short := step_higher_short P hk hnext
  render := stepRender P hk hnext
  birth := stepBirth P
  birth_ranks := step_birth_ranks P
  render_base := step_render_base P hk hnext
  lawful := step_render_lawful P hk hnext
  bound {_} _ S _ _ {_ _} hH hb _ := PairedSlotDecoder.decode_le hH (fun _ ha => by
    obtain ⟨f, hf⟩ := PairedSlotEncoding.mem_values.mp ha; simpa only [← hf] using hb f) _
  supported {_} _ _ _ _ {_ _ _} hl hH _ := PairedSlotDecoder.decode_supported hl hH _
  agreement {j} hj S T hS hT hp ht {G H h} hG hH hh hhH hab := by
    obtain ⟨e, heG, he, hpe, hqe, hcompare⟩ := exists_common_cut hG hH hH hh hhH hhH hp ht hab
    have he' : Agree (M.fields (k + 1) (stepNormalized hj S hS hp))
        (M.fields (k + 1) (stepNormalized hj T hT ht)) e := by
      rw [stepNormalized, stepNormalized, M.normalized_fields, M.normalized_fields]; exact he
    exact Agree.decode (step_source_agreement P hk hnext _ _ heG he')
      (PairedSlotDecoder.decode_witness hG hH).mono (PairedSlotDecoder.decode_witness hG hH).mono
      hpe hqe (fun _ _ => hcompare _)
  ceiling_at {j} hj S hS hp {G H} _ hH hb i hi hik := by
    by_cases he : i = k + 1
    · subst i
      refine ⟨(stepController P hnext (stepNormalized hj S hS hp)).1,
        (stepController P hnext _).2, ?_⟩
      unfold stepRender stepSource
      rw [ScopedSourcePrefixLayer.Data.profile_diagonal]
      exact decode_reserved_ceiling hH hb
    · obtain ⟨c, hc, hv⟩ := P.ceiling_at (Nat.le_succ k) (M.state (stepNormalized hj S hS hp))
        (M.state_admissible _) (M.state_proper _)
        (fun _ (hz : _ ∈ stepGrid P) => (sourceGrid_visible hz).mono (Nat.le_succ k))
        ((sourceGrid_visible (sourceGrid_endpoint le_rfl)).mono (Nat.le_succ k))
        (fun d => by rw [M.state_profile]; exact M.anchor_bound _ d) i hi (by have := M.hA; omega)
      refine ⟨stepOld P hnext c, (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans hc, ?_⟩
      unfold stepRender; rw [step_source_old]
      exact (congrArg (PairedSlotDecoder.decode (k + 1)
        (PairedSlotEncoding.values (M.profile S)) G H) hv).trans (decode_reserved_ceiling hH hb)

end Step

def build : (t : ℕ) → t + 2 ≤ A.card → Layer M (t + 2)
  | 0, _ => initial M
  | t + 1, ht => successor (build t (by have := M.hA; omega)) (by have := M.hA; omega) (by have := M.hA; omega)

theorem build_plan (t : ℕ) (ht : t + 2 ≤ A.card) :
    (build M t ht).carrier.plan = I.boundary.plan := by
  induction t with
  | zero => dsimp only [build, initial]; rfl
  | succ _ ih => exact ih (by have := M.hA; omega)

theorem build_coded (t : ℕ) (ht : t + 2 ≤ A.card) :
    (build M t ht).rows.IsCoded := by
  induction t with
  | zero =>
    dsimp only [build, initial]
    let J := input M
    apply CanonicalCodingSupport.layer J.lower
      (M.Anchor 2)
      2 (by decide) M.hA J.separation J.lowerRows J.rows
      (RelativeLadderLayer.coded I.boundary I.rows (by have := M.hA; omega)
        M.field (M.fields 1) M.proper I.coded) J.inherited_row
    intro a d
    change IsCodedLabel 2 ((succRows M).E (succLeaf M a) d)
    rw [succ_leaf_row]
    exact CanonicalCodingSupport.supported (fun _ hz => CanonicalCodingSupport.grid _ _ hz)
      (field_coded M a) (succ_source_supported M a d.1)
  | succ t ih =>
    dsimp only [build, successor]
    let P := build M t (by have := M.hA; omega)
    apply CanonicalCodingSupport.layer P.carrier (M.Anchor (t + 3)) (t + 3)
      (Nat.succ_pos _) ht (P.separated (by have := M.hA; omega)) P.rows
      (stepRows P (by have := M.hA; omega) ht) (ih (by have := M.hA; omega)) (step_inherited_row P (by have := M.hA; omega) ht)
    intro a d
    change IsCodedLabel (t + 3) ((stepRows P (by have := M.hA; omega) ht).E (stepController P ht a).1 d)
    rw [(stepData P (by have := M.hA; omega) ht).row_new (stepController P ht a) d]
    exact CanonicalCodingSupport.supported (fun _ hz => CanonicalCodingSupport.grid _ _ hz)
      (field_coded M a) (step_source_supported P (by have := M.hA; omega) ht a d.1)

def initFace {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    ExactSemanticFace oldRows (succRows M) :=
  let J := input M
  let lowerFace := SeparatedLayerFace.face I.boundary
    (RelativeLadderLayer.Point (X := M.Fld) (Q := M.Anchor 1))
    1 Nat.one_pos (by have := M.hA; omega) (RelativeLadderLayer.separated I.boundary M.proper)
    I.rows J.lowerRows
    (RelativeLadderLayer.inherited_row I.boundary I.rows (by have := M.hA; omega) M.field (M.fields 1) M.proper) G hT
  SeparatedLayerFace.face J.lower
    (M.Anchor 2) 2
    (by decide) M.hA J.separation J.lowerRows J.rows J.inherited_row lowerFace hT

def buildFace {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T) :
    (t : ℕ) → (ht : t + 2 ≤ A.card) → ExactSemanticFace oldRows (build M t ht).rows
  | 0, _ => initFace M G hT
  | t + 1, ht =>
    let P := build M t (by have := M.hA; omega)
    SeparatedLayerFace.face P.carrier (M.Anchor (t + 3)) (t + 3)
      (Nat.succ_pos _) ht (P.separated (by have := M.hA; omega)) P.rows (stepRows P (by have := M.hA; omega) ht)
      (step_inherited_row P (by have := M.hA; omega) ht) (buildFace G hT t (by have := M.hA; omega)) hT

theorem buildFace_map {T : Finset ι} {E : CellScheme T} {oldRows : Semantics E}
    (G : ExactSemanticFace oldRows I.rows) (hT : ¬ A ⊆ T)
    (t : ℕ) (ht : t + 2 ≤ A.card) (d : Cell E) :
    (buildFace M G hT t ht).map d =
      (build M t ht).baseMap (RelativeLadderLayer.old I.boundary (by have := M.hA; omega) (G.map d)) := by
  induction t with
  | zero => dsimp only [buildFace, build, initial]; rfl
  | succ t ih => exact congrArg (stepOld (build M t (by have := M.hA; omega)) ht) (ih (by have := M.hA; omega))

def donorFace (hB : B ⊂ A) (t : ℕ) (ht : t + 2 ≤ A.card) :
    ExactSemanticFace I.leftRows (build M t ht).rows :=
  buildFace M I.leftFace hB.not_ge t ht

def privateFace (hC : C ⊂ A) (t : ℕ) (ht : t + 2 ≤ A.card) :
    ExactSemanticFace I.rightRows (build M t ht).rows :=
  buildFace M I.rightFace hC.not_ge t ht

theorem donor_order (hB : B ⊂ A) (t : ℕ) (ht : t + 2 ≤ A.card) :
    StrictMono (donorFace M hB t ht).map := by
  have he := funext (buildFace_map M I.leftFace hB.not_ge t ht)
  change StrictMono (buildFace M I.leftFace hB.not_ge t ht).map
  rw [he]
  exact (build M t ht).base_mono.comp ((SourceLayerCarrier.old_order _ _ _ _ _).comp I.left_order)

theorem private_order (hC : C ⊂ A) (t : ℕ) (ht : t + 2 ≤ A.card) :
    StrictMono (privateFace M hC t ht).map := by
  have he := funext (buildFace_map M I.rightFace hC.not_ge t ht)
  change StrictMono (buildFace M I.rightFace hC.not_ge t ht).map
  rw [he]
  exact (build M t ht).base_mono.comp ((SourceLayerCarrier.old_order _ _ _ _ _).comp I.right_order)

theorem full_occupied (t : ℕ) (ht : t + 2 ≤ A.card) (j : ℕ) (hj : 1 ≤ j) (hjt : j ≤ t + 2) :
    ∃ d, (build M t ht).carrier.cell d = (A, j) := by
  obtain ⟨d, hd, _⟩ := (build M t ht).ceiling_at le_rfl
    M.zeroSt (M.zero_admissible t) M.zero_proper
    (G := ∅) (H := ⊤) (by simp) (by simp [SelfVis]) (fun _ => le_top) j hj hjt
  exact ⟨d, hd⟩

end
end VaughtConjecture.Knight.PaddedTower
