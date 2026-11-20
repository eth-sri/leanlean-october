/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ScopedSourcePrefixLayer

/-! # Installing a family of selected lower sections

Extend each old section by common-prefix comparisons on the new controllers.
The ordinary, padded and marked (weighted) layers all have this same lower
matrix. The controller labels may repeat a family member.
-/

@[expose] public section
namespace VaughtConjecture.Knight
open Transform Value ExtOrd SourcePrefixRows SourcePrefixLayer
noncomputable section
variable {ι X Q : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {N : ℕ}

structure SourceFamily (D : CellScheme A) (N : ℕ) (X Q : Type*) where
  sem : Semantics D
  positive : 0 < N
  height : N ≤ A.card
  separated : ∀ d : Cell D, ¬ GradedLe (A, N) (D.cell d)
  fields : Q → X → ExtOrd
  grid : Finset ExtOrd
  bot_mem : ⊥ ∈ grid
  ceiling : ExtOrd
  ceiling_mem : ceiling ∈ grid
  grid_bound : ∀ h ∈ grid, h ≤ ceiling
  grid_visible : ∀ h ∈ grid, SelfVis N h
  lower : Q → Cell D → ExtOrd
  lower_lawful : ∀ a, RespectsSemanticsBelow sem (A, N) (fun d => lower a d.1)
  lower_bound : ∀ a d, D.grade d ≤ N → lower a d ≤ ceiling
  lower_prefix : ∀ a b h, h ∈ grid → Agree (fields a) (fields b) h →
    ∀ d, D.grade d ≤ N → min (lower a d) h = min (lower b d) h

namespace SourceFamily
variable (I : SourceFamily D N X Q) {T : Type*} [Fintype T]

abbrev carrier := SourceLayerCarrier.scheme D T N I.positive I.height
abbrev old (d : Cell D) := SourceLayerCarrier.toCell D T N I.positive I.height (.inl d)
abbrev controller := SourceLayerCarrier.controller D T N I.positive I.height
abbrev member := (SeparatedSourceLayerCarrier.controllerEquiv D T N I.positive I.height I.separated).symm
abbrev ownerEquiv := SeparatedSourceLayerCarrier.ownerEquiv D T N I.positive I.height I.separated

theorem member_controller (a : T) : I.member (I.controller a) = a := Equiv.symm_apply_apply _ _
theorem old_index (d : Cell D) : (I.carrier (T := T)).cell (I.old d) = D.cell d :=
  SourceLayerCarrier.cell_toCell _ _ _ _ _ _

def lowerVector (a : Q) (d : Cell (I.carrier (T := T))) : ExtOrd :=
  match SourceLayerCarrier.toOcc D (T) N I.positive I.height d with
  | .inl x => I.lower a x
  | .inr _ => ⊥

theorem lowerVector_old (a : Q) (d : Cell D) :
    I.lowerVector a ((old I (T := T) d)) = I.lower a d := by
  simp only [lowerVector, old, SourceLayerCarrier.toOcc_toCell]

variable (label : T → Q)

def data : ScopedSourcePrefixLayer.Data (I.carrier (T := T)) N X where
  base := SeparatedSourceLayerCarrier.base D (T) N
    I.positive I.height I.separated I.sem
  separated c hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (T) N
      I.positive I.height c hc
    rw [SourceLayerCarrier.cell_toCell]
    exact I.separated x
  grid := I.grid
  bot_mem := I.bot_mem
  ceiling := I.ceiling
  ceiling_mem := I.ceiling_mem
  grid_bound := I.grid_bound
  grid_visible := I.grid_visible
  boundary q := I.fields (label (I.member q))
  lower q := I.lowerVector (label (I.member q))
  lower_bound q d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (T) N
      I.positive I.height d hd
    rw [lowerVector_old]
    exact I.lower_bound _ x (by simpa only [CellScheme.grade, old_index] using hg)
  lower_lawful q c hg hc := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (T) N
      I.positive I.height c hc
    apply (SeparatedSourceLayerCarrier.base_respects_iff D (T) N
      I.positive I.height I.separated I.sem x _).mpr
    have hx : GradedLe (D.cell x) (A, N) :=
      ⟨D.isPlan.subset_of_mem (D.scope_mem_plan x), by
        simpa only [CellScheme.grade, SourceLayerCarrier.cell_toCell,
          SourceLayerCarrier.index] using hg⟩
    simpa only [Function.comp_def, SeparatedSourceLayerCarrier.ownerEquiv_val,
      lowerVector_old, CellScheme.below.mono] using (I.lower_lawful _).mono hx
  grid_agreement p q h hh hag d hg hd := by
    obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D (T) N
      I.positive I.height d hd
    simpa only [lowerVector_old] using I.lower_prefix _ _ h hh hag x
      (by simpa only [CellScheme.grade, old_index] using hg)

theorem base_consistent (hs : I.sem.IsConsistent) (c : Cell (I.carrier (T := T)))
    (hc : (I.carrier (T := T)).cell c ≠ (A,N)) :
    RespectsSemanticsBelow (I.data label).base ((I.carrier (T := T)).cell c) ((I.data label).base.E c) := by
  obtain ⟨x, rfl⟩ := SourceLayerCarrier.old_occurrence D T N I.positive I.height c hc
  apply (SeparatedSourceLayerCarrier.base_respects_iff D T N I.positive I.height I.separated I.sem x _).mpr
  simpa only [Function.comp_def, data, SeparatedSourceLayerCarrier.base_old] using hs x

variable [Fintype Q]
abbrev source (a : Q) := (I.data id).profile (I.controller a)

theorem source_old (a : Q) (d : Cell D) : I.source a (I.old d) = I.lower a d := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_old _ _
    (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separated d)]
  change I.lowerVector (I.member (I.controller a)) (I.old (T := Q) d) = _
  rw [member_controller, lowerVector_old]

theorem source_new (a b : Q) : I.source a (I.controller b).1 = cut I.grid (I.fields a) (I.fields b) := by
  rw [source, ScopedSourcePrefixLayer.Data.profile_new]
  simp only [data, member_controller, id_eq]

theorem source_supported (a : Q) (hs : ∀ d, OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.lower a d))
    (d : Cell (I.carrier (T := Q))) : OrbitPrefixSupport.Supported N (I.grid : Set ExtOrd) (I.fields a) (I.source a d) := by
  obtain ⟨v, rfl⟩ := (SourceLayerCarrier.enumeration D Q N I.positive I.height).surjective d
  cases v with
  | inl x => exact (I.source_old a x).symm ▸ hs x
  | inr b => exact (I.source_new a b).symm ▸ Or.inr (Or.inl (cut_mem I.bot_mem _ _))

theorem source_agrees {a b : Q} {h : ExtOrd} (hh : h ∈ I.grid) (hf : Agree (I.fields a) (I.fields b) h)
    (hs : Agree (I.lower a) (I.lower b) h) : Agree (I.source a) (I.source b) h := by
  intro d
  obtain ⟨v, rfl⟩ := (SourceLayerCarrier.enumeration D Q N I.positive I.height).surjective d
  cases v with
  | inl x =>
    change min (I.source a (I.old x)) h = min (I.source b (I.old x)) h
    simpa only [I.source_old] using hs x
  | inr c =>
    exact (I.data id).profile_prefix (p := I.controller a) (q := I.controller b) hh
      (by simpa only [data, member_controller, id_eq] using hf)
      ⟨(I.controller c).1, by rw [(I.controller c).2]; exact GradedLe.refl _⟩

theorem inherited_row (c : Cell D) (d : D.below (D.cell c)) :
    (I.data label).rows.E (I.old (T := T) c) (I.ownerEquiv c d) = I.sem.E c d := by
  rw [ScopedSourcePrefixLayer.Data.row_old _ (SeparatedSourceLayerCarrier.old_not_full _ _ _ _ _ I.separated c)]
  exact SeparatedSourceLayerCarrier.base_old _ _ _ _ _ _ _ c d

end SourceFamily
end
end VaughtConjecture.Knight
