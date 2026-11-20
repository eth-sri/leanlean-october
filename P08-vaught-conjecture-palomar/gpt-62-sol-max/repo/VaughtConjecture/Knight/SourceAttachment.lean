/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.SeparatedSourceLayerCarrier
public import VaughtConjecture.Knight.ScopedSourcePrefixLayer
public import VaughtConjecture.Knight.AmbientGradeCharts
public import VaughtConjecture.Knight.PairedSlotComparison

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd SourcePrefixRows PairedSlotComparison SharpWitnessComposition

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

structure AttachmentGrid (k : ℕ) where
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis k h
namespace AttachmentGrid

abbrev endpoint (k n : ℕ) : ExtOrd := ofOrd (Ordinal.omega0 * (2 * n + 1 : ℕ) + k)

noncomputable def canonical (k n : ℕ) : AttachmentGrid k where
  grid := sourceGrid k n
  bot_mem := sourceGrid_bot _ _
  ceiling := endpoint k n
  ceiling_mem := sourceGrid_endpoint le_rfl
  grid_visible _ := sourceGrid_visible
  grid_bound h hh := by
    classical
    rcases Finset.mem_insert.mp hh with rfl | hh
    · exact bot_le
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hh
      have hb' : b ≤ 2 * n + 1 := by grind
      exact ofOrd_le_ofOrd.mpr (add_le_add (by gcongr) le_rfl)

end AttachmentGrid

/-- A separated extension is specified on the old carrier. Transport of its rows and
profiles to actual occurrences is the same at every grade. -/
structure SourceAttachment (D : CellScheme A) (k : ℕ) (X Q : Type*) extends AttachmentGrid k where
  sem : Semantics D
  pos : 0 < k
  height : k ≤ A.card
  separated : ∀ d : Cell D, ¬ GradedLe (A, k) (D.cell d)
  fields : Q → X → ExtOrd
  lower : Q → Cell D → ExtOrd
  lower_bound : ∀ a d, D.grade d ≤ k → lower a d ≤ ceiling
  lower_lawful : ∀ a, RespectsSemanticsBelow sem (A, k) (fun d => lower a d.1)
  lower_prefix : ∀ a b h, h ∈ grid → Agree (fields a) (fields b) h →
    ∀ d, D.grade d ≤ k → min (lower a d) h = min (lower b d) h

namespace SourceAttachment

noncomputable section

variable {D : CellScheme A} {k : ℕ} {X Q : Type*} [Fintype Q]
  (I : SourceAttachment D k X Q)

/-- Reindex the catalogue without changing the predecessor or its rows. -/
abbrev comap {P : Type*} (f : P → Q) : SourceAttachment D k X P where
  toAttachmentGrid := I.toAttachmentGrid
  sem := I.sem
  pos := I.pos
  height := I.height
  separated := I.separated
  fields := I.fields ∘ f
  lower := I.lower ∘ f
  lower_bound a := I.lower_bound (f a)
  lower_lawful a := I.lower_lawful (f a)
  lower_prefix a b := I.lower_prefix (f a) (f b)

abbrev carrier := SourceLayerCarrier.scheme D Q k I.pos I.height

abbrev old (d : Cell D) : Cell I.carrier := SourceLayerCarrier.toCell D Q k I.pos I.height (.inl d)

abbrev controller := SeparatedSourceLayerCarrier.controller D Q k I.pos I.height

abbrev controllerEquiv := SeparatedSourceLayerCarrier.controllerEquiv D Q k I.pos I.height I.separated

abbrev member := I.controllerEquiv.symm

abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv D Q k I.pos I.height I.separated

@[simp] theorem member_controller (a : Q) : I.member (I.controller a) = a :=
  I.controllerEquiv.symm_apply_apply a

@[simp] theorem old_index (d : Cell D) : I.carrier.cell (I.old d) = D.cell d :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

theorem old_grade (d : Cell D) : I.carrier.grade (I.old d) = D.grade d :=
  congrArg Prod.snd (I.old_index d)

theorem old_not_full (d : Cell D) : I.carrier.cell (I.old d) ≠ (A, k) :=
  SeparatedSourceLayerCarrier.old_not_full D Q k I.pos I.height I.separated d

theorem old_occurrence {d : Cell I.carrier} (hd : I.carrier.cell d ≠ (A, k)) :
    ∃ x, d = I.old x := SourceLayerCarrier.old_occurrence D Q k I.pos I.height d hd

theorem cell_cases (d : Cell I.carrier) : (∃ x, d = I.old x) ∨ ∃ a, d = (I.controller a).1 := by
  obtain ⟨x | a, rfl⟩ := (SourceLayerCarrier.enumeration D Q k I.pos I.height).surjective d
  · exact Or.inl ⟨x, rfl⟩
  · exact Or.inr ⟨a, rfl⟩

def liftLower (a : Q) (d : Cell I.carrier) : ExtOrd :=
  match SourceLayerCarrier.toOcc D Q k I.pos I.height d with
  | .inl x => I.lower a x
  | .inr _ => ⊥

@[simp] theorem liftLower_old (a : Q) (d : Cell D) : I.liftLower a (I.old d) = I.lower a d := by
  simp only [liftLower, old, SourceLayerCarrier.toOcc_toCell]

abbrev base := SeparatedSourceLayerCarrier.base D Q k I.pos I.height I.separated I.sem

theorem base_respects (c : Cell D) (q : Cell I.carrier → ExtOrd) :
    RespectsSemanticsBelow I.base (I.carrier.cell (I.old c)) (fun d => q d.1) ↔
      RespectsSemanticsBelow I.sem (D.cell c) (fun d => q (I.old d.1)) :=
  SeparatedSourceLayerCarrier.base_respects_iff D Q k I.pos I.height I.separated I.sem c (fun d => q d.1)

theorem base_row (c : Cell D) (d : D.below (D.cell c)) :
    I.base.E (I.old c) (I.ownerEquiv c d) = I.sem.E c d :=
  SeparatedSourceLayerCarrier.base_old D Q k I.pos I.height I.separated I.sem c d

def data : ScopedSourcePrefixLayer.Data I.carrier k X where
  base := I.base
  separated c hc := by
    obtain ⟨d, rfl⟩ := I.old_occurrence hc
    rw [I.old_index]
    exact I.separated d
  grid := I.grid
  bot_mem := I.bot_mem
  ceiling := I.ceiling
  ceiling_mem := I.ceiling_mem
  grid_bound := I.grid_bound
  grid_visible := I.grid_visible
  boundary c := I.fields (I.member c)
  lower c := I.liftLower (I.member c)
  lower_bound c d hg hd := by
    obtain ⟨x, rfl⟩ := I.old_occurrence hd
    rw [I.liftLower_old]
    exact I.lower_bound _ x ((I.old_grade x).symm.trans_le hg)
  lower_lawful c d hg hd := by
    obtain ⟨x, rfl⟩ := I.old_occurrence hd
    apply (I.base_respects x (I.liftLower (I.member c))).mpr
    simp only [I.liftLower_old]
    exact (I.lower_lawful (I.member c)).mono
      ⟨D.scope_subset x, (I.old_grade x).symm.trans_le hg⟩
  grid_agreement a b h hh hag d hg hd := by
    obtain ⟨x, rfl⟩ := I.old_occurrence hd
    simp only [I.liftLower_old]
    exact I.lower_prefix _ _ _ hh hag x ((I.old_grade x).symm.trans_le hg)

@[simp] theorem data_boundary (a : Q) : I.data.boundary (I.controller a) = I.fields a := by
  simp only [data, I.member_controller]

abbrev rows := I.data.rows

abbrev source (a : Q) := I.data.profile (I.controller a)

theorem source_old (a : Q) (d : Cell D) : I.source a (I.old d) = I.lower a d := by
  rw [source, I.data.profile_old _ (I.old_not_full d)]
  simp only [data, I.member_controller, I.liftLower_old]

theorem source_new (a b : Q) :
    I.source a (I.controller b).1 = cut I.grid (I.fields a) (I.fields b) := by
  rw [source, I.data.profile_new, I.data_boundary, I.data_boundary]
  rfl

theorem source_supported (hl : ∀ a d, OrbitPrefixSupport.Supported k (I.grid : Set ExtOrd)
      (I.fields a) (I.lower a d)) (a : Q) (d : Cell I.carrier) :
    OrbitPrefixSupport.Supported k (I.grid : Set ExtOrd) (I.fields a) (I.source a d) := by
  rcases I.cell_cases d with ⟨x, rfl⟩ | ⟨b, rfl⟩
  · rw [I.source_old]; exact hl a x
  · rw [I.source_new]; exact Or.inr (Or.inl (cut_mem I.bot_mem _ _))

theorem source_prefix {a b : Q} {h : ExtOrd} (hh : h ∈ I.grid)
    (hag : Agree (I.fields a) (I.fields b) h) (hl : Agree (I.lower a) (I.lower b) h) :
    Agree (I.source a) (I.source b) h := by
  intro d
  rcases I.cell_cases d with ⟨x, rfl⟩ | ⟨c, rfl⟩
  · simpa only [I.source_old] using hl x
  · rw [I.source_new, I.source_new]
    simpa only [min_assoc, min_eq_right (le_cut hh hag)] using
      congrArg (min · h) (cross_agreement I.bot_mem (I.fields a) (I.fields b) (I.fields c))

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    I.rows.E (I.old c) (I.ownerEquiv c d) = I.sem.E c d := by
  rw [I.data.row_old (I.old_not_full c)]
  exact I.base_row c d

theorem higher_short (l : ℕ)
    (hsrc : ∀ a d, SharpWitnessComposition.Short k (I.source a d))
    (hbase : ∀ c : Cell D, D.scope c = A → l ≤ D.grade c →
      ∀ d : D.below (D.cell c), SharpWitnessComposition.Short (D.grade c) (I.sem.E c d))
    (c : Cell I.carrier) (hs : I.carrier.scope c = A) (hg : l ≤ I.carrier.grade c)
    (d : I.carrier.below (I.carrier.cell c)) :
    SharpWitnessComposition.Short (I.carrier.grade c) (I.rows.E c d) := by
  rcases I.cell_cases c with ⟨x, rfl⟩ | ⟨a, rfl⟩
  · obtain ⟨e, rfl⟩ := (I.ownerEquiv x).surjective d
    rw [I.inherited_row, I.old_grade]
    exact hbase x ((congrArg Prod.fst (I.old_index x)).symm.trans hs) (hg.trans_eq (I.old_grade x)) e
  · rw [I.data.row_new (I.controller a), show I.carrier.grade (I.controller a).1 = k from
      congrArg Prod.snd (I.controller a).2]
    exact hsrc a d.1

theorem old_respects (c : Cell D) (q : Cell I.carrier → ExtOrd) :
    RespectsSemanticsBelow I.rows (I.carrier.cell (I.old c)) (fun d => q d.1) ↔
      RespectsSemanticsBelow I.sem (D.cell c) (fun d => q (I.old d.1)) :=
  (I.data.old_respects_iff (I.old_not_full c)).trans (I.base_respects c q)

theorem base_consistent (hs : I.sem.IsConsistent) (c : Cell I.carrier)
    (hc : I.carrier.cell c ≠ (A, k)) :
    RespectsSemanticsBelow I.base (I.carrier.cell c) (I.base.E c) := by
  obtain ⟨d, rfl⟩ := I.old_occurrence hc
  exact (SeparatedSourceLayerCarrier.patch D Q k I.pos I.height I.separated).consistent_at
    I.base_row hs d

/-- Check the decoded proper rows on the predecessor rather than on transported cells. -/
theorem decoded_whole (a : Q) {ν : ExtOrd → ExtOrd} (hν : Witness (gTop k) ν)
    (hmax : ∀ d : Cell I.carrier, I.carrier.grade d ≤ k)
    (hproper : ∀ c : Cell D, D.scope c ≠ A →
      RespectsSemanticsBelow I.sem (D.cell c) (fun d => ν (I.lower a d.1)))
    (hshort : ∀ c : Cell I.carrier, I.carrier.scope c = A → ∀ d : I.carrier.below (I.carrier.cell c),
      Short (I.carrier.grade c) (I.rows.E c d)) :
    RespectsSemantics I.rows (ν ∘ I.source a) := by
  apply I.data.decoded_respects_whole hmax (I.controller a) le_rfl hν _ hshort
  intro c hc
  obtain ⟨x, rfl⟩ := I.old_occurrence (fun he => hc (congrArg Prod.fst he))
  apply (I.base_respects x (ν ∘ I.liftLower (I.member (I.controller a)))).mpr
  simpa only [Function.comp_apply, I.liftLower_old, I.member_controller] using
    hproper x (fun h => hc ((congrArg Prod.fst (I.old_index x)).trans h))

theorem consistent (hs : I.sem.IsConsistent) : I.rows.IsConsistent :=
  I.data.consistent (I.base_consistent hs)

theorem exists_chart (seed : Q) {q : I.carrier.below (A, k) → ExtOrd}
    (hq : RespectsSemanticsBelow I.rows (A, k) q) :
    ∃ a σ H, Witness (gTop k) σ ∧ (∀ d, I.carrier.grade d.1 = k → q d ≤ H) ∧
      ∀ d, σ (I.source a d.1) = min (q d) H :=
  AmbientGradeCharts.exists_chart_of_rows hq seed (fun a => (I.controller a).1)
    (fun a => (I.controller a).2)
    (fun c hc => ⟨I.member ⟨c, hc⟩, (congrArg Subtype.val (I.controllerEquiv.apply_symm_apply ⟨c, hc⟩)).symm⟩)
    I.source (fun a => I.data.row_new (I.controller a))

end

end SourceAttachment

end VaughtConjecture.Knight
