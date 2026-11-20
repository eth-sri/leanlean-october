/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CappedDonorCatalogue
public import VaughtConjecture.Knight.CanonicalFieldLayer
public import VaughtConjecture.Knight.FinalGateDecoding

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
  exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr; omega) le_rfl)

theorem member_gate_visible (a : Member R) : SelfVis N (a.val .gate) := by
  obtain ⟨st, -, -, hg, he⟩ := a.property.2
  rw [← he]
  rwa [st.sourceProfile_of_present (f := .gate) R.one_le_N]

include R in
theorem req_grade_le (d : Cell P.scheme) : P.scheme.grade d ≤ N :=
  (Ref.gradeP_le d).trans (R.arity_lt).le

include R in
theorem field_grade_le (f : Field P C) : f.grade ≤ N := by
  cases f with
  | req d => exact req_grade_le R d
  | priv d => exact gradeC_le d
  | gate => exact R.one_le_N

/-- No future fields remain when the acquired context has arity `N`. -/
theorem profile_present (st : R.State N) (f : Field P C) :
    st.sourceProfile f = st.numeric f (field_grade_le R f) :=
  st.sourceProfile_of_present (field_grade_le R f)

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

/-- Install the catalogue with the common canonical grid. Only predecessor
semantics and source-section data are supplied; all new rows are constructed. -/
def install (sem : Semantics D) (hA : N ≤ A.card)
    (hsep : ∀ d : Cell D, ¬ GradedLe (A, N) (D.cell d))
    (lower : Member R → Cell D → ExtOrd)
    (hlaw : ∀ a, RespectsSemanticsBelow sem (A, N) (fun d => lower a d.1))
    (hbound : ∀ a d, D.grade d ≤ N →
      lower a d ≤ CanonicalFieldLayer.ceiling N (Field P C))
    (hprefix : ∀ a b h, h ∈ sourceGrid N (Fintype.card (Field P C)) →
      Agree a.val b.val h → ∀ d, D.grade d ≤ N →
        min (lower a d) h = min (lower b d) h) :
    FinalGateLayer.Input D N (Field P C) (Member R) where
  sem := sem
  pos := R.one_le_N
  height := hA
  separated := hsep
  fields a := a.val
  gate := .gate
  toAttachmentGrid := AttachmentGrid.canonical N (Fintype.card (Field P C))
  lower := lower
  lower_lawful := hlaw
  lower_bound := hbound
  lower_prefix := hprefix
  gate_visible := member_gate_visible R
  gate_bound a := member_bound R a .gate

/-- Terminal insertion decodes an admitted vector while preserving its bottom pattern. -/
theorem exists_member_decoder {a : Field P C → ExtOrd} (ha : R.Admitted a) :
    ∃ (b : Member R) (δ : ExtOrd → ExtOrd), Witness (gTop N) δ ∧
      (∀ f, δ (b.val f) = a f) ∧ ∀ f, δ (b.val f) = ⊥ ↔ b.val f = ⊥ := by
  obtain ⟨b, -, -, hp, -, hb, hc, δ, hδ, hr⟩ := ha.exists_terminal 0
  refine ⟨⟨PairedSlotEncoding.normalize N b, hc, hb⟩, δ, hδ, hr, fun f => ?_⟩
  change δ (PairedSlotEncoding.normalize N b f) = ⊥ ↔ _
  rw [hr, PairedSlotEncoding.normalize_bot_iff]
  exact (bottom_pattern_of_cap_agreement (ofOrd_ne_bot 0) hp f).symm

/-- The actual complete field vector has a bottom-reflecting decoder. -/
theorem exists_actual_member_reflecting :
    ∃ (a : Member R) (δ : ExtOrd → ExtOrd), Witness (gTop N) δ ∧
      (∀ d : Cell P.scheme, δ (a.val (.req d)) = R.p d) ∧
      (∀ d : Cell C.scheme, δ (a.val (.priv d)) = R.vact d) ∧
      δ (a.val .gate) = ⊤ ∧
      ∀ f, δ (a.val f) = ⊥ ↔ a.val f = ⊥ := by
  let st := resync (R.actualState N)
  obtain ⟨a, δ, hδ, hr, hb⟩ := exists_member_decoder R
    ⟨st, (R.actual_admissible N).resync, resync_synchronized (R.actual_admissible N),
      TopSupport.selfVis_top_ext N, rfl⟩
  exact ⟨a, δ, hδ, fun d => (hr _).trans (profile_present R st (.req d)),
    fun d => (hr _).trans (profile_present R st (.priv d)),
    (hr _).trans (profile_present R st .gate), hb⟩

end

end VaughtConjecture.Knight.OrdinaryFinalCatalogue
