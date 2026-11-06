/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.DuplicationPlan
public import VaughtConjecture.Knight.ExtendOneWith
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # The finite carrier for a rounded-meet one-point extension

Use the duplicated plan, copy every old cell at every fresh visible scope
with the same folded scope, and add the grade-`K` term and a mute apex.
The old cells occur first and their face restriction is literally unchanged.
Multiplicity at old indices is retained. Completeness is proved from old
completeness, not assumed of the new carrier.

This file constructs geometry and occurrences only. The intended rows are
described by `RoundedMeetRow`; their installation and whole-scheme legality
remain separate obligations.
-/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight.RoundedMeetCarrier

open AmalgamationPlan

variable {n : ℕ}

def pointMap : Option (Fin n) ↪ Fin (n + 1) := finSuccEquivLast.symm.toEmbedding

@[simp] theorem pointMap_some (a : Fin n) : pointMap (some a) = Fin.castSuccEmb a :=
  finSuccEquivLast_symm_some a

@[simp] theorem pointMap_none : pointMap (none : Option (Fin n)) = Fin.last n :=
  finSuccEquivLast_symm_none

def fold (v : Fin n) (a : Fin (n + 1)) : Fin n :=
  DuplicationPlan.fold v (finSuccEquivLast a)

@[simp] theorem fold_pointMap (v : Fin n) (a : Option (Fin n)) :
    fold v (pointMap a) = DuplicationPlan.fold v a := by
  simp [fold, pointMap]

@[simp] theorem fold_castSucc (v a : Fin n) : fold v (Fin.castSuccEmb a) = a := by
  change DuplicationPlan.fold v (finSuccEquivLast (Fin.castSucc a)) = a
  simp [DuplicationPlan.fold]

def plan (v : Fin n) (P : Finset (Finset (Fin n))) : Finset (Finset (Fin (n + 1))) :=
  (DuplicationPlan.plan v Finset.univ P).image (Finset.image pointMap)

theorem domain_eq_univ : DuplicationPlan.domain (Finset.univ : Finset (Fin n)) = Finset.univ := by
  ext a
  cases a <;> simp [DuplicationPlan.domain, DuplicationPlan.old]

theorem pointMap_domain :
    (DuplicationPlan.domain (Finset.univ : Finset (Fin n))).image pointMap = Finset.univ := by
  rw [domain_eq_univ]
  exact Finset.image_univ_of_surjective finSuccEquivLast.symm.surjective

theorem isPlan {P : Finset (Finset (Fin n))} (hP : Plan.IsPlan Finset.univ P)
    (v : Fin n) (hv : Finset.univ.erase v ∈ P) : Plan.IsPlan Finset.univ (plan v P) := by
  have h := Plan.isPlan_image pointMap (DuplicationPlan.isPlan hP (Finset.mem_univ v) hv)
  rw [pointMap_domain] at h
  exact h

theorem image_old (B : Finset (Fin n)) :
    (B.image DuplicationPlan.old).image pointMap = B.image Fin.castSuccEmb := by
  simp [Finset.image_image, Function.comp_def]

theorem old_face_iff (v : Fin n) (P : Finset (Finset (Fin n))) (B : Finset (Fin n)) :
    B.image Fin.castSuccEmb ∈ plan v P ↔ B ∈ P := by
  rw [← image_old]
  constructor
  · intro h
    obtain ⟨S, hS, he⟩ := Finset.mem_image.mp h
    have he' := Finset.image_injective pointMap.injective he
    exact (DuplicationPlan.old_face_iff v Finset.univ P B).mp (he' ▸ hS)
  · intro h
    exact Finset.mem_image.mpr ⟨B.image DuplicationPlan.old,
      (DuplicationPlan.old_face_iff v Finset.univ P B).mpr h, rfl⟩

@[simp] theorem image_fold_pointMap (v : Fin n) (S : Finset (Option (Fin n))) :
    (S.image pointMap).image (fold v) = S.image (DuplicationPlan.fold v) := by
  simp [Finset.image_image, Function.comp_def]

variable (C : CellScheme (ι := Fin n) Finset.univ) (v : Fin n)
  (hv : Finset.univ.erase v ∈ C.plan) (K : ℕ) (hK0 : 0 < K) (hKn : K ≤ n)

def newFaces : Finset (Finset (Fin (n + 1))) := (plan v C.plan).filter (Fin.last n ∈ ·)

/-- One copy for each old cell, not just one representative per graded index. -/
abbrev Copy := {p : ↥(newFaces C v) × Cell C // C.scope p.2 = p.1.1.image (fold v)}

/-- `false` names the rounded-meet owner, `true` the mute highest-grade apex. -/
abbrev New := Copy C v ⊕ Bool

noncomputable def newCell : New C v → Finset (Fin (n + 1)) × ℕ
  | .inl p => (p.1.1.1, C.grade p.1.2)
  | .inr false => (Finset.univ, K)
  | .inr true => (Finset.univ, n + 1)

include hv hK0 hKn in
theorem newCell_mem (x : New C v) : newCell C v K x ∈ Plan.gradedPlan (plan v C.plan) := by
  rcases x with p | (_ | _)
  · apply Plan.mem_gradedPlan.mpr
    refine ⟨(Finset.mem_filter.mp p.1.1.2).1, C.grade_pos _, ?_⟩
    have h := C.grade_le_card_scope p.1.2
    rw [p.2] at h
    exact h.trans Finset.card_image_le
  · exact Plan.mem_gradedPlan.mpr ⟨(isPlan C.isPlan v hv).domain_mem, hK0,
      by simpa [newCell] using hKn.trans (Nat.le_succ n)⟩
  · exact Plan.mem_gradedPlan.mpr ⟨(isPlan C.isPlan v hv).domain_mem,
      Nat.zero_lt_succ _, by simp [newCell]⟩

noncomputable def scheme : CellScheme (ι := Fin (n + 1)) Finset.univ :=
  CellScheme.extendOneWith C (plan v C.plan) (isPlan C.isPlan v hv)
    (old_face_iff v C.plan) (newCell C v K) (newCell_mem C v hv K hK0 hKn)

def oldCell (c : Cell C) : Cell (scheme C v hv K hK0 hKn) :=
  Fin.castAdd (Fintype.card (New C v)) c

noncomputable def addedCell (x : New C v) : Cell (scheme C v hv K hK0 hKn) :=
  Fin.natAdd C.card ((Fintype.equivFin (New C v)) x)

@[simp] theorem oldCell_index (c : Cell C) :
    (scheme C v hv K hK0 hKn).cell (oldCell C v hv K hK0 hKn c) =
      ((C.scope c).image Fin.castSuccEmb, C.grade c) :=
  CellScheme.extendOneWith_cell_castAdd c

@[simp] theorem addedCell_index (x : New C v) :
    (scheme C v hv K hK0 hKn).cell (addedCell C v hv K hK0 hKn x) = newCell C v K x := by
  unfold addedCell scheme
  rw [CellScheme.extendOneWith_cell_natAdd, Equiv.symm_apply_apply]

/-- The new full-scope term cell. Its semantic value will be forced, not freely chosen. -/
noncomputable def term : Cell (scheme C v hv K hK0 hKn) :=
  addedCell C v hv K hK0 hKn (.inr false)

noncomputable def apex : Cell (scheme C v hv K hK0 hKn) :=
  addedCell C v hv K hK0 hKn (.inr true)

@[simp] theorem term_index : (scheme C v hv K hK0 hKn).cell (term C v hv K hK0 hKn) =
    (Finset.univ, K) := addedCell_index C v hv K hK0 hKn (.inr false)

@[simp] theorem apex_index : (scheme C v hv K hK0 hKn).cell (apex C v hv K hK0 hKn) =
    (Finset.univ, n + 1) := addedCell_index C v hv K hK0 hKn (.inr true)

end VaughtConjecture.Knight.RoundedMeetCarrier
