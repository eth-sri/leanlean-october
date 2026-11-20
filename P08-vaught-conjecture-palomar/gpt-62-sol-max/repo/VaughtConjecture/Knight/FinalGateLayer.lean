/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WeightedSourcePrefixLayer
public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier

public import VaughtConjecture.Knight.SourceAttachment

@[expose] public section

namespace VaughtConjecture.Knight.FinalGateLayer

open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer

noncomputable section

variable {ι X Q : Type*} [DecidableEq ι] [Fintype Q]

variable {A : Finset ι} {D : CellScheme A} {N : ℕ}

/-- The predecessor data consumed by the actual weighted installation. -/
structure Input (D : CellScheme A) (N : ℕ) (X Q : Type*) extends SourceAttachment D N X Q where
  gate : X
  gate_visible : ∀ a, SelfVis N (fields a gate)
  gate_bound : ∀ a, fields a gate ≤ ceiling

namespace Input

variable (I : Input D N X Q)

abbrev Node := Q × Bool

abbrev attachment := I.toSourceAttachment.comap (P := Node (Q := Q)) Prod.fst

abbrev carrier := I.attachment.carrier

abbrev old := I.attachment.old

abbrev controller := I.attachment.controller

abbrev added (a : Q) (marked : Bool) := (I.controller (a, marked)).1

abbrev member := I.attachment.member

@[simp] theorem member_controller (a : Q) (marked : Bool) :
    I.member (I.controller (a, marked)) = (a, marked) := I.attachment.member_controller _

@[simp] theorem old_index (d : Cell D) : I.carrier.cell (I.old d) = D.cell d :=
  I.attachment.old_index d

@[simp] theorem added_index (a : Q) (marked : Bool) :
    I.carrier.cell (I.added a marked) = (A, N) := (I.controller (a, marked)).2

theorem old_strictMono : StrictMono I.old :=
  by tauto

/-- The old occurrence inventory is exhaustive on every proper scope. -/
theorem proper_occurrence {S : Finset ι} {k : ℕ} (hS : S ⊆ A) (hne : S ≠ A)
    (d : I.carrier.below (S, k)) :
    ∃ x : D.below (S, k), d.1 = I.old x.1 := by
  have hn : I.carrier.cell d.1 ≠ (A, N) := by
    intro he
    exact hne (Finset.Subset.antisymm hS (he ▸ d.2).1)
  obtain ⟨x, hx⟩ := I.attachment.old_occurrence hn
  refine ⟨⟨x, ?_⟩, hx⟩
  simpa only [hx, I.old_index] using d.2

abbrev lowerVector (a : Q) := I.attachment.liftLower (a, false)

theorem lowerVector_old (a : Q) (d : Cell D) :
    I.lowerVector a (I.old d) = I.lower a d := I.attachment.liftLower_old _ _

abbrev data := I.attachment.data

def nodeWeight (v : Node (Q := Q)) : ExtOrd :=
  if v.2 then I.fields v.1 I.gate else I.ceiling

def weight (q : Controller I.carrier N) : ExtOrd := I.nodeWeight (I.member q)

theorem weight_visible (q : Controller I.carrier N) : SelfVis N (I.weight q) := by
  unfold weight nodeWeight
  split
  · exact I.gate_visible _
  · exact I.grid_visible _ I.ceiling_mem

theorem weight_bound (q : Controller I.carrier N) : I.weight q ≤ I.ceiling := by
  unfold weight nodeWeight
  split
  · exact I.gate_bound _
  rfl

theorem weight_kind (q : Controller I.carrier N) :
    I.weight q = I.data.ceiling ∨ ∃ x, I.weight q = I.data.boundary q x := by
  unfold weight nodeWeight
  split
  all_goals tauto

theorem parent (q : Controller I.carrier N) :
    ∃ p, I.data.boundary p = I.data.boundary q ∧ I.weight p = I.data.ceiling := by
  refine ⟨I.controller ((I.member q).1, false), ?_, ?_⟩
  · change I.fields (I.member (I.controller _)).1 = _
    aesop
  · simp only [weight, member_controller, nodeWeight, Bool.false_eq_true, ↓reduceIte]
    rfl

abbrev rows := WeightedSourcePrefixLayer.rows I.data I.weight I.weight_visible

abbrev source (a : Q) :=
  WeightedSourcePrefixLayer.master I.data I.weight (I.controller (a, false))

theorem source_lawful (a : Q) : RespectsSemanticsBelow I.rows (A, N)
    (fun d => I.source a d.1) :=
  WeightedSourcePrefixLayer.master_respects I.data I.weight I.weight_visible I.parent _

theorem source_old (a : Q) (d : Cell D) : I.source a (I.old d) = I.lower a d := by
  rw [source, WeightedSourcePrefixLayer.master_old _ _ _ (I.attachment.old_not_full d)]
  change I.lowerVector (I.member (I.controller (a, false))).1 (I.old d) = _
  rw [member_controller, lowerVector_old]

theorem source_added (a b : Q) (marked : Bool) :
    I.source a (I.added b marked) =
      min (cut I.grid (I.fields a) (I.fields b)) (I.nodeWeight (b, marked)) := by
  rw [source, show I.added b marked = (I.controller (b, marked)).1 from rfl,
    WeightedSourcePrefixLayer.master_new]
  simp [data, SourceAttachment.data, attachment, weight, member_controller]

theorem source_marked (a b : Q) : I.source a (I.added b true) =
    min (I.fields a I.gate) (cut I.grid (I.fields a) (I.fields b)) := by
  rw [source_added]
  change min (cut I.grid (I.fields a) (I.fields b)) (I.fields b I.gate) = _
  rw [min_comm]
  exact (agree_cut I.bot_mem _ _ I.gate).symm

theorem source_marked_le (a b : Q) : I.source a (I.added b true) ≤ I.fields a I.gate := by
  rw [source_marked]
  simp

theorem source_own_marked (a : Q) : I.source a (I.added a true) = I.fields a I.gate := by
  rw [source_marked, cut_refl I.ceiling_mem I.grid_bound, min_eq_left (I.gate_bound a)]

theorem source_bound (a : Q) (d : Cell I.carrier) (hd : I.carrier.grade d ≤ N) :
    I.source a d ≤ I.ceiling :=
  WeightedSourcePrefixLayer.master_bound I.data I.weight _ d hd

theorem leaf_row (a : Q) (d : I.carrier.below (I.carrier.cell (I.added a false))) :
    I.rows.E (I.added a false) d = I.source a d.1 := by
  have hw : I.weight (I.controller (a, false)) = I.ceiling := by
    simp [weight, member_controller, nodeWeight, Bool.false_eq_true, ↓reduceIte]
  exact (WeightedSourcePrefixLayer.row_new I.data I.weight I.weight_visible
    (I.controller (a, false)) d).trans (by
      rw [hw, min_eq_left]
      exact I.source_bound a d.1
        (by simpa only [CellScheme.grade, added_index] using d.2.2))

theorem source_supported
    (hlower : ∀ a d, D.grade d ≤ N →
      OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.lower a d))
    (a : Q) (d : Cell I.carrier) (hd : I.carrier.grade d ≤ N) :
    OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.source a d) := by
  have h := WeightedSourcePrefixLayer.master_supported I.data I.weight I.weight_visible
    I.weight_kind (fun q d hg hn => ?_) (I.controller (a, false)) d hd
  · simpa [source, data, SourceAttachment.data, attachment, member_controller] using h
  · obtain ⟨x, rfl⟩ := I.attachment.old_occurrence hn
    change OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd)
      (I.fields (I.member q).1) (I.lowerVector _ (I.old x))
    rw [lowerVector_old]
    exact hlower _ x ((I.attachment.old_grade x).symm.trans_le hg)

theorem source_prefix (a b : Q) {h : ExtOrd} (hh : h ∈ I.grid)
    (hag : Agree (I.fields a) (I.fields b) h) :
    Agree (fun d : I.carrier.below (A, N) => I.source a d.1)
      (fun d => I.source b d.1) h := by
  apply WeightedSourcePrefixLayer.master_prefix I.data I.weight hh
  simpa [data, SourceAttachment.data, attachment, member_controller] using hag

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    I.rows.E (I.old c) (I.attachment.ownerEquiv c d) = I.sem.E c d := by
  rw [WeightedSourcePrefixLayer.row_old _ _ _ (I.attachment.old_not_full c)]
  exact I.attachment.base_row c d

theorem consistent (hs : I.sem.IsConsistent) : I.rows.IsConsistent :=
  WeightedSourcePrefixLayer.consistent I.data I.weight I.weight_visible I.parent
    (I.attachment.base_consistent hs)

end Input

end

end VaughtConjecture.Knight.FinalGateLayer
