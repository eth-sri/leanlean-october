/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SourceFamily
public import VaughtConjecture.Knight.PaddedTower

/-! # Adding a native catalogue to a padded tower -/

@[expose] public section

namespace VaughtConjecture.Knight.PaddedTower.Step
open Transform Value ExtOrd SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section
variable {ι X : Type*} [DecidableEq ι] [Fintype X] {A : Finset ι} {D : CellScheme A}
  {Q : ℕ → Type*} [∀ j, Fintype (Q j)]
variable {F : System D X Q} {k : ℕ} (P : Layer F k)

abbrev grid (_ : Layer F k) := RecursiveRungRendering.grid X (k + 1)
abbrev ceiling (_ : Layer F k) := RecursiveRungRendering.ceiling X (k + 1)

variable (hk : 1 ≤ k) (hnext : k + 1 ≤ A.card)
abbrev carrier := SourceLayerCarrier.scheme P.carrier (Q (k + 1))
  (k + 1) (Nat.succ_pos k) hnext
abbrev old (d : Cell P.carrier) := SourceLayerCarrier.toCell P.carrier (Q (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (.inl d)
abbrev controller := SourceLayerCarrier.controller P.carrier (Q (k + 1))
  (k + 1) (Nat.succ_pos k) hnext
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv P.carrier (Q (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (P.separated hk)
abbrev member := (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (Q (k + 1))
  (k + 1) (Nat.succ_pos k) hnext (P.separated hk)).symm

include hk in
theorem old_not_full (d : Cell P.carrier) :
    (carrier P hnext).cell (old P hnext d) ≠ (A, k + 1) :=
  SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _
    (P.separated hk) d

def family : SourceFamily P.carrier (k + 1) X (Q (k + 1)) where
  sem := P.rows
  positive := Nat.succ_pos _
  height := hnext
  separated := P.separated hk
  fields := F.values
  lower := P.selected
  lower_lawful := P.lawful
  lower_bound a d _ := P.bound a d
  lower_prefix a b h hh hf d _ := P.agreement a b hh hf d
  grid := grid P
  bot_mem := sourceGrid_bot _ _
  ceiling := ceiling P
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_bound _ hh := CanonicalFieldLayer.grid_bound _ _ hh
  grid_visible _ hh := sourceGrid_visible hh

abbrev data := (family P hk hnext).data id

abbrev rows := (data P hk hnext).rows
abbrev source (a : Q (k + 1)) := (data P hk hnext).profile (controller P hnext a)

theorem source_old (a : Q (k + 1)) (d : Cell P.carrier) :
    source P hk hnext a (old P hnext d) = P.selected a d :=
  (family P hk hnext).source_old a d

theorem source_new (a b : Q (k + 1)) :
    source P hk hnext a (controller P hnext b).1 =
      cut (grid P) (F.values a) (F.values b) :=
  (family P hk hnext).source_new a b

theorem source_lawful (a : Q (k + 1)) :
    RespectsSemanticsBelow (rows P hk hnext) (A, k + 1)
      (fun d => source P hk hnext a d.1) := (data P hk hnext).profile_respects _

theorem source_supported (a : Q (k + 1)) (d : Cell (carrier P hnext)) :
    OrbitPrefixSupport.Supported (k + 1) (grid P : Set ExtOrd) (F.values a)
      (source P hk hnext a d) :=
  (family P hk hnext).source_supported a (P.supported a) d

theorem source_short (a : Q (k + 1)) (d : Cell (carrier P hnext)) :
    Short (k + 1) (source P hk hnext a d) :=
  PairedCoupledSections.supported_short
    (fun _ hh => CanonicalFieldLayer.grid_short _ _ hh)
    (CanonicalPairedProfiles.inventory_short _ _ (F.canonical a)) (source_supported P hk hnext a d)

theorem source_bound (a : Q (k + 1)) (d : Cell (carrier P hnext)) :
    source P hk hnext a d ≤ ceiling P := by
  by_cases hd : (carrier P hnext).cell d = (A, k + 1)
  · exact (data P hk hnext).profile_bound _ d (congrArg Prod.snd hd).le
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (Q (k + 1))
      (k + 1) (Nat.succ_pos k) hnext d hd
    rw [source_old]
    exact P.bound a x

theorem source_agreement (a b : Q (k + 1)) {h : ExtOrd}
    (hh : h ∈ grid P) (hab : Agree (F.values a) (F.values b) h) :
    Agree (source P hk hnext a) (source P hk hnext b) h :=
  (family P hk hnext).source_agrees hh hab (P.agreement a b hh hab)

theorem inherited_row (c : Cell P.carrier) (d : P.carrier.below (P.carrier.cell c)) :
    (rows P hk hnext).E (old P hnext c) (ownerEquiv P hk hnext c d) = P.rows.E c d :=
  (family P hk hnext).inherited_row id c d

theorem old_respects (c : Cell P.carrier) (p : Cell (carrier P hnext) → ExtOrd) :
    RespectsSemanticsBelow (rows P hk hnext) ((carrier P hnext).cell (old P hnext c))
      (fun d => p d.1) ↔
      RespectsSemanticsBelow P.rows (P.carrier.cell c) (fun d => p (old P hnext d.1)) := by
  apply ((data P hk hnext).old_respects_iff (old_not_full P hk hnext c)).trans
  exact SeparatedSourceLayerCarrier.base_respects_iff P.carrier (Q (k + 1))
    (k + 1) (Nat.succ_pos k) hnext (P.separated hk) P.rows c _

theorem consistent : (rows P hk hnext).IsConsistent :=
  (data P hk hnext).consistent ((family P hk hnext).base_consistent id P.consistent)

abbrev baseMap (d : Cell F.base) := old P hnext (P.baseMap d)

theorem base_index (d : Cell F.base) :
    (carrier P hnext).cell (baseMap P hnext d) = F.base.cell d :=
  (SourceLayerCarrier.cell_toCell _ _ _ _ _ _).trans (P.base_index d)

theorem base_row (c : Cell F.base)
    (d : F.base.below (F.base.cell c)) :
    (rows P hk hnext).E (baseMap P hnext c)
      ⟨baseMap P hnext d.1, by simpa only [base_index] using d.2⟩ =
        F.baseRows.E c d :=
  (inherited_row P hk hnext (P.baseMap c)
    ⟨P.baseMap d.1, by simpa only [P.base_index] using d.2⟩).trans (P.base_row c d)

theorem base_respects (c : Cell F.base)
    (p : Cell (carrier P hnext) → ExtOrd) :
    RespectsSemanticsBelow (rows P hk hnext) ((carrier P hnext).cell (baseMap P hnext c))
      (fun d => p d.1) ↔
      RespectsSemanticsBelow F.baseRows
        (F.base.cell c) (fun d => p (baseMap P hnext d.1)) :=
  (old_respects P hk hnext (P.baseMap c) p).trans
    (P.base_respects c (fun d => p (old P hnext d)))

include hk in
theorem cell_cases (d : Cell (carrier P hnext)) :
    (∃ c, d = baseMap P hnext c) ∨
      (carrier P hnext).scope d = A ∧ 2 ≤ (carrier P hnext).grade d ∧
        (carrier P hnext).grade d ≤ k + 1 := by
  obtain ⟨x, rfl⟩ := (SourceLayerCarrier.enumeration P.carrier (Q (k + 1))
    (k + 1) (Nat.succ_pos k) hnext).surjective d
  rcases x with x | a
  · rcases P.cases x with ⟨c, rfl⟩ | ⟨hs, hl, hu⟩
    · exact Or.inl ⟨c, rfl⟩
    · have he := SourceLayerCarrier.cell_toCell P.carrier (Q (k + 1))
        (k + 1) (Nat.succ_pos k) hnext (.inl x)
      exact Or.inr ⟨(congrArg Prod.fst he).trans hs,
        hl.trans_eq (congrArg Prod.snd he).symm,
        (congrArg Prod.snd he).le.trans (hu.trans (Nat.le_succ k))⟩
  · have he := SourceLayerCarrier.cell_toCell P.carrier (Q (k + 1))
      (k + 1) (Nat.succ_pos k) hnext (.inr a)
    exact Or.inr ⟨congrArg Prod.fst he,
      (show 2 ≤ k + 1 by omega).trans_eq (congrArg Prod.snd he).symm,
      (congrArg Prod.snd he).le⟩

theorem higher_short (c : Cell (carrier P hnext)) (hc : (carrier P hnext).scope c = A)
    (hg : 2 ≤ (carrier P hnext).grade c)
    (d : (carrier P hnext).below ((carrier P hnext).cell c)) :
    Short ((carrier P hnext).grade c) ((rows P hk hnext).E c d) := by
  by_cases he : (carrier P hnext).cell c = (A, k + 1)
  · let a := member P hk hnext ⟨c, he⟩
    have ha : controller P hnext a = ⟨c, he⟩ :=
      (SeparatedSourceLayerCarrier.controllerEquiv P.carrier (Q (k + 1))
        (k + 1) (Nat.succ_pos k) hnext
        (P.separated hk)).apply_symm_apply _
    have hr := (data P hk hnext).row_new ⟨c, he⟩ d
    rw [hr, show (carrier P hnext).grade c = k + 1 from congrArg Prod.snd he]
    simpa only [source, ha] using source_short P hk hnext a d.1
  · obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence P.carrier (Q (k + 1))
      (k + 1) (Nat.succ_pos k) hnext c he
    obtain ⟨e, rfl⟩ := (ownerEquiv P hk hnext x).surjective d
    rw [inherited_row]
    have hi := SourceLayerCarrier.cell_toCell P.carrier (Q (k + 1))
      (k + 1) (Nat.succ_pos k) hnext (.inl x)
    change Short ((carrier P hnext).grade (old P hnext x)) _
    rw [show (carrier P hnext).grade (old P hnext x) = P.carrier.grade x from
      congrArg Prod.snd hi]
    exact P.higher_short x ((congrArg Prod.fst hi).symm.trans hc)
      (hg.trans_eq (congrArg Prod.snd hi)) e

theorem source_base (a : Q (k + 1)) (d : Cell F.base) :
    source P hk hnext a (baseMap P hnext d) = F.table (P.birth a) a d :=
  (source_old P hk hnext a (P.baseMap d)).trans (P.render_base a d)

/-- The long base table is the only exception to short-row decoding. This
argument works both for the incoming renderer and for terminal insertion. -/
theorem decoded {j : ℕ} (hj : k + 1 ≤ j) (a : Q (k + 1)) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop (k + 1)) δ)
    (hb : RespectsSemanticsBelow F.baseRows (A, j)
      (fun d => δ (source P hk hnext a (baseMap P hnext d.1)))) :
    RespectsSemanticsBelow (rows P hk hnext) (A,j) (fun d => δ (source P hk hnext a d.1)) := by
  have oldLaw (b : Cell F.base) (h : GradedLe (F.base.cell b) (A,j)) :=
    (base_respects P hk hnext b (fun d => δ (source P hk hnext a d))).mpr (hb.mono h)
  have native : RespectsSemanticsBelow (rows P hk hnext) (A,k+1)
      (fun d => δ (source P hk hnext a d.1)) := by
    apply map_respects_of_short_or_local (source_lawful P hk hnext a) (fun d => d.2.2) hδ
    rintro ⟨c,hc⟩
    rcases cell_cases P hk hnext c with ⟨b,rfl⟩ | ⟨hs,hl,_⟩
    · rw [base_index] at hc
      exact Or.inr ((oldLaw b ⟨hc.1, hc.2.trans hj⟩).locality ⟨_, GradedLe.refl _⟩)
    · exact Or.inl (higher_short P hk hnext c hs hl)
  apply ScopedSourcePrefixLayer.respects_below_of_lower _ _ (fun d => δ (source P hk hnext a d))
  rintro ⟨c,hc⟩
  rcases cell_cases P hk hnext c with ⟨b,rfl⟩ | ⟨hs,_,hu⟩
  · exact oldLaw b (by rwa [base_index] at hc)
  · exact native.mono ⟨hs.subset, hu⟩

theorem decoded_base (a : Q (k + 1)) {δ : ExtOrd → ExtOrd}
    (hδ : Witness (gTop (k + 1)) δ)
    (hreflect : ∀ f, δ (F.values a f) = ⊥ → F.values a f = ⊥)
    (horiginal : RespectsSemanticsBelow F.sem (A, k + 1)
      (fun d => δ (F.values a (F.field d.1)))) :
    RespectsSemanticsBelow F.baseRows (A, k + 1)
      (fun d => δ (source P hk hnext a (baseMap P hnext d.1))) := by
  simp only [source_base, System.table]
  by_cases hz : δ (ceiling P) = ⊥
  · have he (d : Cell F.base) :
        δ (RelativeLadderLayer.renderWith D F.positive F.field (@F.values 1)
          (P.birth a) (F.values a) (ceiling P) d) = ⊥ := by
      change δ (F.table (P.birth a) a d) = _
      rw [← source_base P hk hnext a d]
      exact le_bot_iff.mp ((hδ.mono (source_bound P hk hnext a _)).trans_eq hz)
    simp only [he]
    exact ⟨fun _ => (selfVis_bot _).symm, fun c => by
      simpa only [min_self] using TransformsTo.to_bot (F.baseRows.E c.1),
      fun _ c _ _ => ⟨c, rfl, le_rfl⟩⟩
  · let f := fun i => δ (LadderScalarRendering.level
      (LadderScalarRendering.values (F.values a)) (ceiling P) i)
    apply RelativeLadderLayer.image_respects D F.sem F.positive
      F.field (@F.values 1) F.proper (P.birth a) f
      (hδ.mono.comp (LadderScalarRendering.level_mono
        (LadderScalarRendering.values_bound (F.bounded a))))
      (by simp only [f, LadderScalarRendering.level_zero, hδ.bot])
    · intro i
      have hv := LadderScalarRendering.level_visible (C := ceiling P)
        (F.visible (Nat.succ_pos _) a)
        ((PairedSlotComparison.sourceGrid_visible
          (PairedSlotComparison.sourceGrid_endpoint le_rfl)).mono (Nat.succ_pos k)) i
      have he := hδ.clause5
        (LadderScalarRendering.level (LadderScalarRendering.values (F.values a))
          (ceiling P) i) 1
        (by rw [gTop_of_le (Nat.succ_pos k)]; exact le_top) 1 le_rfl
      change SelfVis 1 (δ _)
      rw [hv] at he
      exact he.symm
    · intro i hi _
      have hp := LadderScalarRendering.level_pos
        (LadderScalarRendering.bot_not_values (F.values a))
        (LadderScalarRendering.values_bound (F.bounded a))
        (fun h => hz (h ▸ hδ.bot)) hi
      rcases LadderScalarRendering.level_supported
          (LadderScalarRendering.values (F.values a)) (ceiling P) i with he | he | he
      · exact (hp he).elim
      · obtain ⟨_, x, hx⟩ := LadderScalarRendering.mem_values.mp he
        intro h
        have hb := hreflect x ((congrArg δ hx).trans h)
        exact hp (hx.symm.trans hb)
      · exact fun h => hz (he ▸ h)
    · simpa only [f, P.birth_ranks, LadderScalarRendering.field_readback] using horiginal

theorem decoded_lawful (a : Q (k + 1)) {δ : ExtOrd → ExtOrd} (hδ : Witness (gTop (k + 1)) δ)
    (hr : ∀ x, δ (F.values a x) = ⊥ → F.values a x = ⊥)
    (hb : RespectsSemanticsBelow F.sem (A,k+1) (fun d => δ (F.values a (F.field d.1)))) :
    RespectsSemanticsBelow (rows P hk hnext) (A,k+1) (fun d => δ (source P hk hnext a d.1)) :=
  decoded P hk hnext le_rfl a hδ (decoded_base P hk hnext a hδ hr hb)

end
end VaughtConjecture.Knight.PaddedTower.Step
