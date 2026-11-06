/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CappedDonorCatalogue
import VaughtConjecture.Knight.CanonicalFieldLayer
import VaughtConjecture.Knight.FinalGateDecoding

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

namespace VaughtConjecture.Knight.OrdinaryFinalCatalogue
open   ExtOrd CappedDonor CappedDonor.Ref SourcePrefixRows
open PairedSlotComparison SharpWitnessComposition
noncomputable section

variable {I : Type*} [Fintype I] {nP N : ℕ}
variable {P : SemScheme (nP + 1)} {C : SemScheme N} (R : Ref I nP N N P C)

abbrev Member := ↥R.Catalogue

instance : Fintype (Member R) := R.catalogue_finite.fintype

def member_short (a : Member R) f :=
  CanonicalPairedProfiles.inventory_short a.property.1 f

local notation "ceiling₀" => CanonicalFieldLayer.ceiling N (Field P C)

theorem member_bound (a : Member R) f :
    a.val f ≤ ceiling₀ := by
  apply (CanonicalPairedProfiles.inventory_bound _ _ a.property.1 f).trans
  exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl)

theorem member_gate_visible (a : Member R) : SelfVis N (a.val .gate) := by
  obtain ⟨st, -, -, hg, he⟩ := a.property.2
  rw [← he]
  rw [st.sourceProfile_of_present (f := .gate) R.one_le_N]
  exact hg

include R in
theorem req_grade_le d : P.scheme.grade d ≤ N :=
  (Ref.gradeP_le d).trans (R.arity_lt).le

include R in
theorem field_grade_le (f : Field P C) : f.grade ≤ N := by
  cases f with
  | req d => exact req_grade_le R d
  | priv d => exact gradeC_le d
  | gate => exact R.one_le_N

/-- No future fields remain when the acquired context has arity `N`. -/
def profile_present {st : R.State N} {f : Field P C} :=
  st.sourceProfile_of_present (field_grade_le R f)

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- Install the catalogue with the common canonical grid. Only predecessor
semantics and source-section data are supplied; all new rows are constructed. -/
def install (sem : Semantics D) (hA : N ≤ A.card)
    (hsep : ∀ d , ¬ GradedLe (A, N) (D.cell d))
    (lower : Member R → CellLabels D)
    (hlaw : ∀ a, RespectsSemanticsBelow sem (A, N) (fun d => lower a d.1))
    (hbound : ∀ a d, D.grade d ≤ N →
      lower a d ≤ ceiling₀)
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
  bot_mem := sourceGrid_bot
  ceiling := ceiling₀
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound hh
  grid_visible _ hh := sourceGrid_visible hh
  lower := lower
  lower_lawful := hlaw
  lower_bound := hbound
  lower_prefix := hprefix
  gate_visible := member_gate_visible R
  gate_bound a := member_bound R a .gate

/-- One catalogue member and one decoder recover the actual complete field
vector. The gate is literally top after decoding, not merely positive. -/
theorem exists_actual_member_reflecting :
    ∃ (a : Member R) (δ : LabelMap), Witness (gTop N) δ ∧
      (∀ d , δ (a.val (.req d)) = R.p d) ∧
      (∀ d : Cell C.scheme, δ (a.val (.priv d)) = R.vact d) ∧
      δ (a.val .gate) = ⊤ ∧
      ∀ f, δ (a.val f) = ⊥ ↔ a.val f = ⊥ := by
  let st := resync (R.actualState N)
  have hadm : R.Admitted st.sourceProfile :=
    ⟨st, (R.actual_admissible N).resync, resync_synchronized (R.actual_admissible N),
      TopSupport.selfVis_top_ext N, rfl⟩
  obtain ⟨b, -, -, hprefix, -, hb, hcan, δ, hδ, hr⟩ := hadm.exists_terminal 0
  refine ⟨⟨PairedSlotEncoding.normalize N b, hcan, hb⟩, δ, hδ, ?_, ?_, ?_, ?_⟩
  · simp_all [profile_present] <;> aesop
  · simp_all [profile_present] <;> aesop
  · simp_all [profile_present] <;> aesop
  · intro f
    rw [hr, PairedSlotEncoding.normalize_bot_iff]
    exact (bottom_pattern_of_cap_agreement (ofOrd_ne_bot 0) hprefix f).symm

/-- The field-level exact display, without its finite reflection receipt. -/
theorem exists_actual_member :
    ∃ (a : Member R) (δ : LabelMap), Witness (gTop N) δ ∧
      (∀ d : Cell P.scheme, δ (a.val (.req d)) = R.p d) ∧
      (∀ d : Cell C.scheme, δ (a.val (.priv d)) = R.vact d) ∧
      δ (a.val .gate) = ⊤ := by
  obtain ⟨a, δ, hw, hP, hC, hg, -⟩ := exists_actual_member_reflecting R
  exact ⟨a, δ, hw, hP, hC, hg⟩

