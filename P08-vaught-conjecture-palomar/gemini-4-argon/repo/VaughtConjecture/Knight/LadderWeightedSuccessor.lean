/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.RelativeLadderRankRendering
public import VaughtConjecture.Knight.WeightedSourcePrefixLayer

/-! # A weighted grade-two successor of the installed ladder

The scalar input distinguishes retained birth-grade anchors from upper sources.
Only an upper source must have a lawful grade-two original restriction. Physical
predecessor lawfulness, bounds and prefix equations are constructed from the
grade-one renderer, including all unused rungs and shadows. Every weighted node
has a separately installed ceiling parent, including nodes of weight bottom.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LadderWeightedSuccessor
open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer

variable {ι X Q U V : Type*} [DecidableEq ι]
  [Fintype X] [Fintype Q] [Fintype U] [Fintype V] {A : Finset ι}

/-- Only original scalar conditions are supplied. None of the physical
predecessor receipts consumed by the weighted installer is a field. -/
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
  nodeField : V → X
  node_visible : ∀ u v, SelfVis 2 (upper u (nodeField v))

namespace Input
variable {D : CellScheme A} (I : Input (X := X) (Q := Q) (U := U) (V := V) D)

abbrev one : 0 < A.card := lt_of_lt_of_le (by decide : 0 < 2) I.height
abbrev lower := RelativeLadderLayer.carrier D I.one (X := X) (Q := Q)
abbrev lowerRows := RelativeLadderLayer.rows D I.sem I.one I.field I.fields I.proper
abbrev Node := U × Option V

local notation "Nd" => Node (U := U) (V := V)
local notation "h2" => (by decide : 0 < 2)

abbrev carrier := SourceLayerCarrier.scheme I.lower Nd 2 h2 I.height
abbrev old (d : Cell I.lower) : Cell I.carrier :=
  SourceLayerCarrier.toCell I.lower Nd 2 h2 I.height (.inl d)
abbrev added (v : Nd) : Cell I.carrier :=
  SourceLayerCarrier.toCell I.lower Nd 2 h2 I.height (.inr v)

omit [Fintype U] [Fintype V] in
theorem separation (d : Cell I.lower) : ¬ GradedLe (A, 2) (I.lower.cell d) := by
  rcases RelativeLadderLayer.cell_cases D I.one d with ⟨x, rfl⟩ | ⟨v, rfl⟩
  · rw [RelativeLadderLayer.old_index]
    exact SeparatedSourceLayerCarrier.separated_of_proper D 2 I.proper x
  · rw [RelativeLadderLayer.added_index]
    exact fun h => (by omega : ¬ 2 ≤ 1) h.2

local notation "old_occ" => SourceLayerCarrier.old_occurrence I.lower Nd 2 h2 I.height
local notation "base_iff" =>
  SeparatedSourceLayerCarrier.base_respects_iff I.lower Nd 2 h2 I.height I.separation I.lowerRows

abbrev controller := SeparatedSourceLayerCarrier.controller I.lower Nd 2 h2 I.height
abbrev member := (SeparatedSourceLayerCarrier.controllerEquiv I.lower Nd 2 h2 I.height I.separation).symm
@[simp] theorem member_controller (v : Nd) :
    I.member (I.controller v) = v := Equiv.symm_apply_apply _ v

def predecessor (u : U) : Cell I.lower → ExtOrd :=
  RelativeLadderLayer.renderWith D I.one I.field I.fields (I.anchor u) (I.upper u) I.ceiling

omit [Fintype U] [Fintype V] in
theorem predecessor_bound (u : U) (d : Cell I.lower) : I.predecessor u d ≤ I.ceiling :=
  RelativeLadderLayer.renderWith_bound D I.one I.field I.fields _ _ (I.bounded u) d

def lowerVector (u : U) (d : Cell I.carrier) : ExtOrd :=
  match SourceLayerCarrier.toOcc I.lower Nd 2 h2 I.height d with
  | .inl x => I.predecessor u x
  | .inr _ => ⊥

theorem lowerVector_old (u : U) (d : Cell I.lower) :
    I.lowerVector u (I.old d) = I.predecessor u d := by
  simp only [lowerVector, old, SourceLayerCarrier.toOcc_toCell]

def data : ScopedSourcePrefixLayer.Data I.carrier 2 X where
  base := SeparatedSourceLayerCarrier.base I.lower Nd 2 h2 I.height I.separation I.lowerRows
  separated c hc := by
    obtain ⟨x, rfl⟩ := old_occ c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact I.separation x
  grid := I.grid
  bot_mem := I.bot_mem
  ceiling := I.ceiling
  ceiling_mem := I.ceiling_mem
  grid_bound := I.grid_bound
  grid_visible := I.grid_visible
  boundary q := I.upper (I.member q).1
  lower q := I.lowerVector (I.member q).1
  lower_bound q d _ hd := by
    obtain ⟨x, rfl⟩ := old_occ d hd
    rw [lowerVector_old]; exact I.predecessor_bound _ x
  lower_lawful q c hg hc := by
    obtain ⟨x, rfl⟩ := old_occ c hc
    apply (base_iff x _).mpr
    change RespectsSemanticsBelow I.lowerRows _ (fun d => I.lowerVector _ (I.old d.1))
    have hx : GradedLe (I.lower.cell x) (A, 2) :=
      ⟨I.lower.isPlan.subset_of_mem (I.lower.scope_mem_plan x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell,
          SourceLayerCarrier.index] using hg⟩
    have hl : RespectsSemanticsBelow I.lowerRows (A, 2) (fun d => I.predecessor (I.member q).1 d.1) :=
      RelativeLadderLayer.renderWith_respects D I.sem I.one I.field I.fields I.proper _ _
        (I.rank_match _) (I.bounded _) (I.visible _)
        ((I.grid_visible _ I.ceiling_mem).mono (by decide)) (I.incoming _)
    simpa only [lowerVector_old, CellScheme.below.mono] using hl.mono hx
  grid_agreement p q h hh hag d _ hd := by
    obtain ⟨x, rfl⟩ := old_occ d hd
    simpa only [lowerVector_old, predecessor] using
      RelativeLadderLayer.renderWith_agreement D I.one I.field I.fields
        (I.rank_match _) (I.rank_match _) (I.bounded _) (I.bounded _) (I.grid_bound h hh) hag x

def nodeWeight (v : Nd) : ExtOrd :=
  match v.2 with
  | none => I.ceiling
  | some x => I.upper v.1 (I.nodeField x)
def weight (q : Controller I.carrier 2) : ExtOrd := I.nodeWeight (I.member q)

theorem weight_visible (q : Controller I.carrier 2) : SelfVis 2 (I.weight q) := by
  unfold weight nodeWeight; split
  · exact I.grid_visible _ I.ceiling_mem
  · exact I.node_visible _ _

theorem parent (q : Controller I.carrier 2) :
    ∃ p, I.data.boundary p = I.data.boundary q ∧ I.weight p = I.data.ceiling :=
  ⟨I.controller ((I.member q).1, none),
    by change I.upper (I.member (I.controller _)).1 = _; rw [member_controller]; rfl,
    by simp only [weight, member_controller, nodeWeight]; rfl⟩

abbrev rows := WeightedSourcePrefixLayer.rows I.data I.weight I.weight_visible
abbrev source (u : U) := WeightedSourcePrefixLayer.master I.data I.weight (I.controller (u, none))

theorem source_lawful (u : U) : RespectsSemanticsBelow I.rows (A, 2)
    (fun d => I.source u d.1) :=
  WeightedSourcePrefixLayer.master_respects I.data I.weight I.weight_visible I.parent _

theorem inherited_row (c : Cell I.lower) (d : I.lower.below (I.lower.cell c)) :
    I.rows.E (I.old c) (SeparatedSourceLayerCarrier.ownerEquiv I.lower Nd
      2 h2 I.height I.separation c d) = I.lowerRows.E c d := by
  rw [WeightedSourcePrefixLayer.row_old _ _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separation c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ I.separation _ c d

theorem consistent (hs : I.sem.IsConsistent) : I.rows.IsConsistent := by
  apply WeightedSourcePrefixLayer.consistent I.data I.weight I.weight_visible I.parent
  intro c hc
  obtain ⟨x, rfl⟩ := old_occ c hc
  apply (base_iff x _).mpr
  simpa only [Function.comp_def, data, SeparatedSourceLayerCarrier.base_old] using
    RelativeLadderLayer.consistent D I.sem I.one I.field I.fields I.proper hs I.birth x

theorem source_old (u : U) (d : Cell I.lower) : I.source u (I.old d) = I.predecessor u d := by
  rw [source, WeightedSourcePrefixLayer.master_old _ _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separation d)]
  change I.lowerVector (I.member (I.controller (u, none))).1 (I.old d) = _
  rw [member_controller, lowerVector_old]

theorem source_original (u : U) (d : Cell D) :
    I.source u (I.old (RelativeLadderLayer.old D I.one d)) = I.upper u (I.field d) := by
  rw [source_old]
  exact RelativeLadderLayer.renderWith_old D I.one I.field I.fields _ _ _ (I.rank_match u) d

theorem source_parent (u : U) : I.source u (I.added (u, none)) = I.ceiling := by
  change WeightedSourcePrefixLayer.master I.data I.weight (I.controller (u, none))
    (I.controller (u, none)).1 = _
  rw [WeightedSourcePrefixLayer.master_new]
  change min (cut I.grid _ _) (I.weight (I.controller (u, none))) = _
  simp only [data, member_controller, weight, nodeWeight]
  rw [cut_refl I.ceiling_mem I.grid_bound, min_self]

omit [Fintype U] [Fintype V] in
theorem predecessor_supported (u : U) (d : Cell I.lower) :
    OrbitPrefixSupport.Supported 2 (I.grid : Set ExtOrd) (I.upper u)
      (I.predecessor u d) := by
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
  · apply WeightedSourcePrefixLayer.master_prefix I.data I.weight hh (q := I.controller (v, none))
      (p := I.controller (u, none)) ?_ ⟨d, hd.symm ▸ GradedLe.refl _⟩
    change Agree (I.upper (I.member (I.controller _)).1)
      (I.upper (I.member (I.controller _)).1) h
    simpa only [member_controller] using hag
  · obtain ⟨x, rfl⟩ := old_occ d hd
    rw [source_old, source_old]
    exact RelativeLadderLayer.renderWith_agreement D I.one I.field I.fields
      (I.rank_match u) (I.rank_match v) (I.bounded u) (I.bounded v) (I.grid_bound h hh) hag x

theorem source_supported_all (u : U) (d : Cell I.carrier) :
    OrbitPrefixSupport.Supported 2 (I.grid : Set ExtOrd)
      (I.upper u) (I.source u d) := by
  by_cases hd : I.carrier.cell d = (A, 2)
  · have h := WeightedSourcePrefixLayer.master_supported I.data I.weight I.weight_visible
      (fun q => by
        unfold weight nodeWeight; split
        · exact Or.inl rfl
        · exact Or.inr ⟨I.nodeField _, rfl⟩)
      (fun q d _ hn => by
        obtain ⟨x, rfl⟩ := old_occ d hn
        change OrbitPrefixSupport.Supported 2 (I.grid : Set ExtOrd)
          (I.upper (I.member q).1) (I.lowerVector _ (I.old x))
        rw [lowerVector_old]
        exact I.predecessor_supported (I.member q).1 x)
      (I.controller (u, none)) d (by simp only [CellScheme.grade, hd, le_refl])
    simpa only [source, data, member_controller] using h
  · obtain ⟨x, rfl⟩ := old_occ d hd
    rw [source_old]
    exact I.predecessor_supported u x

theorem source_bound_all (u : U) (d : Cell I.carrier) : I.source u d ≤ I.ceiling := by
  by_cases hd : I.carrier.cell d = (A, 2)
  · exact WeightedSourcePrefixLayer.master_bound I.data I.weight _ d
      (by simp only [CellScheme.grade, hd, le_refl])
  · obtain ⟨x, rfl⟩ := old_occ d hd
    rw [source_old]
    exact I.predecessor_bound u x

theorem leaf_row (a : U) (d : I.carrier.below (I.carrier.cell (I.added (a, none)))) :
    I.rows.E (I.added (a, none)) d = I.source a d.1 := by
  have he := WeightedSourcePrefixLayer.row_new I.data I.weight I.weight_visible
    (I.controller (a, none)) d
  have hw : I.weight (I.controller (a, none)) = I.ceiling := by
    simp only [weight, member_controller, nodeWeight]
  exact he.trans ((congrArg (min (I.source a d.1)) hw).trans
    (min_eq_left (I.source_bound_all a d.1)))

theorem source_leaf (a b : U) :
    I.source a (I.added (b, none)) = cut I.grid (I.upper a) (I.upper b) := by
  change WeightedSourcePrefixLayer.master I.data I.weight
    (I.controller (a, none)) (I.controller (b, none)).1 = _
  rw [WeightedSourcePrefixLayer.master_new]
  simp only [data, member_controller, weight, nodeWeight]
  exact min_eq_left (cut_le I.grid_bound _ _)

omit [Fintype V] in
theorem cell_cases_empty (I : Input (X := X) (Q := Q) (U := U) (V := Empty) D)
    (d : Cell I.carrier) :
    (∃ x, d = I.old x) ∨ ∃ a, d = I.added (a, none) := by
  obtain ⟨x, hx⟩ := (SourceLayerCarrier.enumeration I.lower
    (Node (U := U) (V := Empty)) 2 h2 I.height).surjective d
  change SourceLayerCarrier.toCell _ _ _ _ _ x = d at hx
  rcases x with x | ⟨a, (_ | v)⟩
  · exact Or.inl ⟨x, hx.symm⟩
  · exact Or.inr ⟨a, hx.symm⟩
  · exact Empty.elim v
