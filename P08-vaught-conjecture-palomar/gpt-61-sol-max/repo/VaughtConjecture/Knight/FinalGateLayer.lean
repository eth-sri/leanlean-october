/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.WeightedSourcePrefixLayer
import VaughtConjecture.Knight.SeparatedSourceLayerCarrier

/-! # A physical final-grade gate layer

Install two distinct full-scope occurrences per source: a ceiling leaf and a
marked node weighted by the source's gate field. The gate field participates in
the comparison cut. Its value must be visible at the installed grade, not merely
at grade one. The parent exists even when the marked weight is bottom.

This is the weighted final layer of new31 / `uniform_upper_receiving`, built on
the actual ordered source-layer carrier using KVC's weighted installer. Lawful
predecessor sources and their common-grid agreement are inputs; this file does
not construct the ordinary scope recursion, an admitted catalogue, or lifting.
No shortness condition is imposed on inherited rows.
-/

namespace VaughtConjecture.Knight.FinalGateLayer
open    SourcePrefixRows 
noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]
variable {A : Finset ι} {D : CellScheme A} {N : ℕ}

/-- The predecessor data consumed by the actual weighted installation. -/
structure Input (D : CellScheme A) (N : ℕ) (X Q : Type*) where
  sem : Semantics D
  positive : 0 < N
  height : N ≤ A.card
  separated : ∀ d , ¬ GradedLe (A, N) (D.cell d)
  fields : Q → X → ExtOrd
  gate : X
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis N h
  lower : Q → CellLabels D
  lower_lawful : ∀ a, RespectsSemanticsBelow sem (A, N) (fun d => lower a d.1)
  lower_bound : ∀ a d, D.grade d ≤ N → lower a d ≤ ceiling
  lower_prefix : ∀ a b h, h ∈ grid → Agree (fields a) (fields b) h →
    ∀ d, D.grade d ≤ N → min (lower a d) h = min (lower b d) h
  gate_visible : ∀ a, SelfVis N (fields a gate)
  gate_bound : ∀ a, fields a gate ≤ ceiling

namespace Input
variable (I : Input D N X Q)

abbrev Node := Q × Bool
local notation "Node₀" => Node (Q := Q)

abbrev carrier := SourceLayerCarrier.scheme D (Node₀) N I.positive I.height
abbrev old (d : Cell D) : Cell I.carrier :=
  SourceLayerCarrier.toCell D (Node₀) N I.positive I.height (.inl d)
abbrev added (a : Q) (marked : Bool) : Cell I.carrier :=
  SourceLayerCarrier.toCell D (Node₀) N I.positive I.height (.inr (a, marked))
abbrev controller := SeparatedSourceLayerCarrier.controller D (Node₀)
  N I.positive I.height
abbrev member := (SeparatedSourceLayerCarrier.controllerEquiv D (Node₀)
  N I.positive I.height I.separated).symm

@[simp] theorem member_controller a marked :
    I.member (I.controller (a, marked)) = (a, marked) := Equiv.symm_apply_apply _ _

@[simp] theorem old_index d : I.carrier.cell (I.old d) = D.cell d :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

@[simp] theorem added_index a marked :
    I.carrier.cell (I.added a marked) = (A, N) :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

theorem old_strictMono : StrictMono I.old :=
  SourceLayerCarrier.old_order

/-- The old occurrence inventory is exhaustive on every proper scope. -/
theorem proper_occurrence {S} {k} (hS : S ⊆ A) (hne : S ≠ A)
    (d : I.carrier.below (S, k)) :
    ∃ x : D.below (S, k), d.1 = I.old x.1 := by
  have hn : I.carrier.cell d.1 ≠ (A, N) := by
    intro he
    exact hne (Finset.Subset.antisymm hS (he ▸ d.2).1)
  obtain ⟨x, hx⟩ := SourceLayerCarrier.old_occurrence D (Node₀) N
    I.positive I.height d.1 hn
  refine ⟨⟨x, ?_⟩, hx⟩
  simpa only [hx, I.old_index] using d.2

def lowerVector a d :=
  match SourceLayerCarrier.toOcc D (Node₀) N I.positive I.height d with
  | .inl x => I.lower a x
  | .inr _ => ⊥

theorem lowerVector_old a d :
    I.lowerVector a (I.old d) = I.lower a d := by
  simp  [lowerVector,  ]

def data : ScopedSourcePrefixLayer.Data I.carrier N X where
  base := SeparatedSourceLayerCarrier.base D (Node₀) N
    I.positive I.height I.separated I.sem
  separated c hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node₀) N
      I.positive I.height c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact I.separated x
  grid := I.grid
  bot_mem := I.bot_mem
  ceiling := I.ceiling
  ceiling_mem := I.ceiling_mem
  grid_bound := I.grid_bound
  grid_visible := I.grid_visible
  boundary q := I.fields (I.member q).1
  lower q := I.lowerVector (I.member q).1
  lower_bound q d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node₀) N
      I.positive I.height d hd
    rw [lowerVector_old]
    exact I.lower_bound _ x (by simpa only [CellScheme.grade, old_index] using hg)
  lower_lawful q c hg hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node₀) N
      I.positive I.height c hc
    apply (SeparatedSourceLayerCarrier.base_respects_iff I.separated I.sem x _).mpr
    have hx : GradedLe (D.cell x) (A, N) :=
      ⟨D.scope_subset x, by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell,
          SourceLayerCarrier.index] using hg⟩
    simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
      lowerVector_old, CellScheme.below.mono] using (I.lower_lawful _).mono hx
  grid_agreement p q h hh hag d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node₀) N
      I.positive I.height d hd
    simpa only [lowerVector_old] using I.lower_prefix _ _ h hh hag x
      (by simpa only [CellScheme.grade, old_index] using hg)

def nodeWeight (v : Node₀) :=
  if v.2 then I.fields v.1 I.gate else I.ceiling
def weight q := I.nodeWeight (I.member q)

theorem weight_visible q : SelfVis N (I.weight q) := by
  unfold weight nodeWeight
  split
  · exact I.gate_visible _
  · exact I.grid_visible _ I.ceiling_mem

theorem weight_bound q : I.weight q ≤ I.ceiling := by
  unfold weight nodeWeight
  split
  · exact I.gate_bound _
  · exact le_rfl

theorem weight_kind q :
    I.weight q = I.data.ceiling ∨ ∃ x, I.weight q = I.data.boundary q x := by
  unfold weight nodeWeight
  split
  · exact Or.inr ⟨I.gate, rfl⟩
  · exact Or.inl rfl

theorem parent q :
    ∃ p, I.data.boundary p = I.data.boundary q ∧ I.weight p = I.data.ceiling := by
  refine ⟨I.controller ((I.member q).1, false), ?_, ?_⟩
  · change I.fields (I.member (I.controller _)).1 = _
    rw [member_controller]
    rfl
  · simp_all [weight] <;> aesop

abbrev rows := WeightedSourcePrefixLayer.rows I.data I.weight I.weight_visible
abbrev source a :=
  WeightedSourcePrefixLayer.master I.data I.weight (I.controller (a, false))

theorem source_lawful a : RespectsSemanticsBelow I.rows (A, N)
    (fun d => I.source a d.1) :=
  WeightedSourcePrefixLayer.master_respects I.data I.weight I.weight_visible I.parent _

theorem source_old a d : I.source a (I.old d) = I.lower a d := by
  rw [source, WeightedSourcePrefixLayer.master_old _ _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ I.separated)]
  change I.lowerVector (I.member (I.controller (a, false))).1 (I.old d) = _
  rw [member_controller, lowerVector_old]

theorem source_added a b marked :
    I.source a (I.added b marked) =
      min (cut I.grid (I.fields a) (I.fields b)) (I.nodeWeight (b, marked)) := by
  rw [source, show I.added b marked = (I.controller (b, marked)).1 from rfl,
    WeightedSourcePrefixLayer.master_new]
  simp  [data, weight, ]

theorem source_marked a b : I.source a (I.added b true) =
    min (I.fields a I.gate) (cut I.grid (I.fields a) (I.fields b)) := by
  rw [source_added]
  
  rw [min_comm]
  exact (agree_cut I.bot_mem _ _ I.gate).symm

theorem source_marked_le a b : I.source a (I.added b true) ≤ I.fields a I.gate := by
  rw [source_marked]
  exact min_le_left _ _

theorem source_own_marked a : I.source a (I.added a true) = I.fields a I.gate := by
  rw [source_marked, cut_refl I.ceiling_mem I.grid_bound, min_eq_left (I.gate_bound a)]

theorem source_own_leaf a : I.source a (I.added a false) = I.ceiling := by
  rw [source_added, cut_refl I.ceiling_mem I.grid_bound]
  exact min_self _

theorem source_bound a d (hd : I.carrier.grade d ≤ N) :
    I.source a d ≤ I.ceiling :=
  WeightedSourcePrefixLayer.master_bound I.data I.weight _ d hd

theorem leaf_row a d :
    I.rows.E (I.added a false) d = I.source a d.1 := by
  have hw : I.weight (I.controller (a, false)) = I.ceiling := by
    simp_all [weight, nodeWeight]
  exact (WeightedSourcePrefixLayer.row_new I.data I.weight I.weight_visible
    (I.controller (a, false)) d).trans (by
      rw [hw, min_eq_left]
      exact I.source_bound a d.1
        (by simpa only [CellScheme.grade, added_index] using d.2.2))

local notation "Supported₀" => OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd)

theorem source_supported
    (hlower : ∀ a d, D.grade d ≤ N →
      Supported₀ (I.fields a) (I.lower a d))
    a d (hd : I.carrier.grade d ≤ N) :
    Supported₀ (I.fields a) (I.source a d) := by
  have h := WeightedSourcePrefixLayer.master_supported I.data I.weight I.weight_visible
    I.weight_kind (fun q d hg hn => ?_) (I.controller (a, false)) d hd
  · simp_all [source, data]
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node₀) N
      I.positive I.height d hn
    change Supported₀
      (I.fields (I.member q).1) (I.lowerVector _ (I.old x))
    rw [lowerVector_old]
    exact hlower _ x (by simpa only [CellScheme.grade, old_index] using hg)

theorem source_prefix a b {h} (hh : h ∈ I.grid)
    (hag : Agree (I.fields a) (I.fields b) h) :
    Agree (fun d : I.carrier.below (A, N) => I.source a d.1)
      (fun d => I.source b d.1) h := by
  apply WeightedSourcePrefixLayer.master_prefix I.data I.weight hh
  simpa only [data, member_controller] using hag

theorem inherited_row c d :
    I.rows.E (I.old c) (SeparatedSourceLayerCarrier.ownerEquiv D (Node₀)
      N I.positive I.height I.separated c d) = I.sem.E c d := by
  rw [WeightedSourcePrefixLayer.row_old _ _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ I.separated)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ I.separated _ d

theorem consistent (hs : I.sem.IsConsistent) : I.rows.IsConsistent := by
  apply WeightedSourcePrefixLayer.consistent I.data I.weight I.weight_visible I.parent
  intro c hc
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (Node₀) N
    I.positive I.height c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff I.separated I.sem x _).mpr
  simpa only [Function.comp_def, data, SeparatedSourceLayerCarrier.base_old] using hs x

