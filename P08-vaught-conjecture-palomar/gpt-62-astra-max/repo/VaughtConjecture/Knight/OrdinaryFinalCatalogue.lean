/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorCatalogue
public import VaughtConjecture.Knight.CanonicalFieldLayer
public import VaughtConjecture.Knight.FinalGateDecoding

/-! # The ordinary catalogue on the actual final gate layer

Use the finite ordinary catalogue, including its gate-off members, as the
controller inventory of `FinalGateLayer`. Gate visibility, field bounds and
shortness follow from catalogue membership. Predecessor sources and their
whole-coordinate prefix agreement remain inputs to the installer; no scope
recursion or bountifulness is asserted here.

The actual donor/private vector has a catalogue representative with one faithful
decoder, including literal tops and an active gate. This is a field-level
selected-display producer, not yet lawfulness of its physical rendering.

The scalar catalogue is V-C's (`04276e9`, updated to `7a1deef` with the
unprimed APIs preserved). The physical layer uses KVC's weighted installer
and the reviewer's final-gate construction.
-/

@[expose] public section

namespace VaughtConjecture.Knight.OrdinaryFinalCatalogue
open Transform Value ExtOrd CappedDonor CappedDonor.Ref SourcePrefixRows
open PairedSlotComparison SharpWitnessComposition
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)

abbrev Member := ↥R.Catalogue

instance : Fintype (Member R) := R.catalogue_finite.fintype

theorem member_short (a : Member R) (f : Field P C) : Short N (a.val f) :=
  CanonicalPairedProfiles.inventory_short _ _ a.property.1 f

theorem member_bound (a : Member R) (f : Field P C) :
    a.val f ≤ CanonicalFieldLayer.ceiling N (Field P C) := by
  apply (CanonicalPairedProfiles.inventory_bound _ _ a.property.1 f).trans
  exact ofOrd_le_ofOrd.mpr (add_le_add (by simp) le_rfl)

theorem member_gate_visible (a : Member R) : SelfVis N (a.val .gate) := a.property.2.gate

include R in
theorem req_grade_le (d : Cell P.scheme) : P.scheme.grade d ≤ N :=
  (Ref.gradeP_le d).trans (R.arity_lt).le

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- Install the catalogue with the common canonical grid. Only predecessor
semantics and source-section data are supplied; all new rows are constructed. -/
def install (sem : Semantics D) (hA : N ≤ A.card)
    (hsep : ∀ d : Cell D, ¬ GradedLe (A, N) (D.cell d))
    (lower : Member R → D.Labelling)
    (hlaw : ∀ a, RespectsSemanticsBelow sem (A, N) (fun d => lower a d.1))
    (hbound : ∀ a d, D.grade d ≤ N →
      lower a d ≤ CanonicalFieldLayer.ceiling N (Field P C))
    (hprefix : ∀ a b h, h ∈ sourceGrid N (Fintype.card (Field P C)) →
      Agree a.val b.val h → ∀ d, D.grade d ≤ N →
        min (lower a d) h = min (lower b d) h) :
    FinalGateLayer.Input D N (Field P C) (Member R) where
  sem := sem
  positive := R.one_le_N
  height := hA
  separated := hsep
  fields a := a.val
  gate := .gate
  grid := sourceGrid N (Fintype.card (Field P C))
  bot_mem := sourceGrid_bot _ _
  ceiling := CanonicalFieldLayer.ceiling N (Field P C)
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound N (Field P C) hh
  grid_visible _ hh := sourceGrid_visible hh
  lower := lower
  lower_lawful := hlaw
  lower_bound := hbound
  lower_prefix := hprefix
  gate_visible := member_gate_visible R
  gate_bound a := member_bound R a .gate

/-- A canonical all-bottom seed suffices for availability and completeness. -/
def seed : Member R := ⟨_, (Admitted.zero R).normalize_mem_catalogue (fun _ => bot_ne_top)⟩

theorem actual : R.Admitted (pack R.p R.vact ⊤) where
  donor := R.p_respects
  priv := R.vact_respects
  face d := (R.face_actual d).symm
  gate := TopSupport.selfVis_top_ext N
  active _ _ := ⟨R.vactL_respects,R.cap_pos.ne',fun i => (R.vact_ref i).trans_ne (ofOrd_ne_bot _),
    fun d hd => (R.face_actual d).trans hd⟩
  relation _ _ d := (R.sel_actual d).symm

end
end VaughtConjecture.Knight.OrdinaryFinalCatalogue
