
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyCompleteFields
import VaughtConjecture.Knight.PartialSections

/-! # Literal common-root transport for the gate-free LOW family

The input records occurrence and row identities, not a supplied repair or a
lawfulness-transport conclusion. The latter and opposite-face installation are
derived from those identities and the two original schemes' bountifulness.
-/

namespace VaughtConjecture.Knight.LowOnly

open     CappedDonor

variable {n : ℕ} {P C : SemScheme n}

/-- The complete common root, with exact original source rows. -/
structure CommonRoot (P C : SemScheme n) where
  A : FiniteScope n
  B : FiniteScope n
  A_mem : A ∈ P.scheme.plan
  B_mem : B ∈ C.scheme.plan
  face : P.scheme.below (A, A.card) ≃ C.scheme.below (B, B.card)
  grade : ∀ a, P.scheme.grade a.1 = C.scheme.grade (face a).1
  scope : ∀ a b, P.scheme.scope a.1 ⊆ P.scheme.scope b.1 ↔
    C.scheme.scope (face a).1 ⊆ C.scheme.scope (face b).1
  row : ∀ a
    d
    hd,
    P.rows.E a.1 d = C.rows.E (face a).1 ⟨(face ⟨d.1, d.2.trans a.2⟩).1, hd⟩

namespace CommonRoot

variable (R : CommonRoot P C)

/-- Every specified common occurrence is carried by the literal root equivalence. -/
abbrev Covers {α : Sort*} (f : α → Cell P.scheme) (g : α → Cell C.scheme) : Prop :=
  ∀ i, ∃ a : P.scheme.below (R.A, R.A.card), a.1 = f i ∧ (R.face a).1 = g i

def fullP {j} (a : P.scheme.below (faceIndex R.A j)) :
    P.scheme.below (R.A, R.A.card) :=
  ⟨a.1, a.2.1, a.2.2.trans (min_le_left _ _)⟩

def fullC {j} (a : C.scheme.below (faceIndex R.B j)) :
    C.scheme.below (R.B, R.B.card) :=
  ⟨a.1, a.2.1, a.2.2.trans (min_le_left _ _)⟩

def faceAt j : P.scheme.below (faceIndex R.A j) ≃
    C.scheme.below (faceIndex R.B j) where
  toFun a := ⟨(R.face (R.fullP a)).1, (R.face (R.fullP a)).2.1,
    le_min (R.face (R.fullP a)).2.2
      ((R.grade (R.fullP a)).symm.trans_le (a.2.2.trans (min_le_right _ _)))⟩
  invFun a := ⟨(R.face.symm (R.fullC a)).1, (R.face.symm (R.fullC a)).2.1,
    le_min (R.face.symm (R.fullC a)).2.2 (by
      have hg := R.grade (R.face.symm (R.fullC a))
      rw [Equiv.apply_symm_apply] at hg
      exact hg.trans_le (a.2.2.trans (min_le_right _ _)))⟩
  left_inv a := by
    apply Subtype.ext
    change (R.face.symm (R.face (R.fullP a))).1 = a.1
    exact congrArg Subtype.val (R.face.symm_apply_apply (R.fullP a))
  right_inv a := by
    apply Subtype.ext
    change (R.face (R.face.symm (R.fullC a))).1 = a.1
    exact congrArg Subtype.val (R.face.apply_symm_apply (R.fullC a))

theorem at_grade {j} (a : P.scheme.below (faceIndex R.A j)) :
    P.scheme.grade a.1 = C.scheme.grade (R.faceAt j a).1 := R.grade (R.fullP a)

/-- Lawfulness transport is proved from every actual row identity. -/
theorem respects_iff {j} v :
    RespectsSemanticsBelow C.rows (faceIndex R.B j) v ↔
      RespectsSemanticsBelow P.rows (faceIndex R.A j) (fun a => v (R.faceAt j a)) := by
  have h := respects_iff_of_equiv   (R.faceAt j)
    R.at_grade (fun a b => R.scope (R.fullP a) (R.fullP b))
    (fun a d hd => R.row (R.fullP a) d hd) (fun a => v (R.faceAt j a))
  simpa only [Function.comp_def, Equiv.apply_symm_apply] using h.symm

def Shared (u : CellLabels P.scheme) (v : CellLabels C.scheme) :=
  ∀ a, u a.1 = v (R.face a).1

theorem shared_at {u : CellLabels P.scheme} {v : CellLabels C.scheme}
    (h : R.Shared u v) {j : ℕ} (a : P.scheme.below (faceIndex R.A j)) :
    u a.1 = v (R.faceAt j a).1 := h (R.fullP a)

local notation "mono₀" => CellScheme.below.mono (faceIndex_le)

/-- Installing the present vector keeps the entire common root, including its future part. -/
theorem shared_complete {j : ℕ} {u : CellLabels P.scheme} {v : CellLabels C.scheme}
    (h : R.Shared u v) (u' : BelowLabels P.scheme (effC n j))
    (v' : BelowLabels C.scheme (effC n j))
    (hface : ∀ a ,
      u' (mono₀ a) =
        v' (mono₀ (R.faceAt j a))) :
    R.Shared (completeAt u u') (completeAt v v') := by
  intro a
  by_cases hj : P.scheme.grade a.1 ≤ j
  · let a' : P.scheme.below (faceIndex R.A j) := ⟨a.1, a.2.1, le_min a.2.2 hj⟩
    exact (completeAt_present u u' (mono₀ a')).trans
      ((hface a').trans
        (completeAt_present v v' (mono₀
          (R.faceAt j a'))).symm)
  · rw [completeAt_future u u' a.1 (not_le.mp hj),
      completeAt_future v v' (R.face a).1 (by rw [← R.grade]; exact not_le.mp hj)]
    exact h a

/-- Prescribe the private root in the original donor, preserving all donor caps.
Empty roots and nominal grade zero need no bountifulness call. -/
theorem installP {j} {u}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    {v}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    {γ} (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ a ,
      min (u (mono₀ a)) γ =
        min (v (mono₀ (R.faceAt j a))) γ) :
    ∃ u', RespectsSemanticsBelow P.rows (effC n j) u' ∧
      (CappedEq u' u γ) ∧
      ∀ a ,
        u' (mono₀ a) =
          v (mono₀ (R.faceAt j a)) := by
  by_cases hk : 0 < min R.A.card j
  · exact P.bountiful.extend (faceIndex_mem R.A_mem hk)
      (effC_mem (hk.trans_le (min_le_right _ _))
        ((hk.trans_le (min_le_left _ _)).trans_le (by exact?)))
      (faceIndex_le) ((R.respects_iff _).mp (hv.mono (faceIndex_le)))
      hu hγ hag
  · exact ⟨u, hu, fun _ => rfl, fun a => (faceIndex_absent hk a).elim⟩

/-- The reverse original-face installation uses the inverse actual root map. -/
theorem installC {j} {v}
    (hv : RespectsSemanticsBelow C.rows (effC n j) v)
    {u}
    (hu : RespectsSemanticsBelow P.rows (effC n j) u)
    {γ} (hγ : SelfVis (effC n j).2 γ)
    (hag : ∀ a ,
      min (v (mono₀ (R.faceAt j a))) γ =
        min (u (mono₀ a)) γ) :
    ∃ v', RespectsSemanticsBelow C.rows (effC n j) v' ∧
      (CappedEq v' v γ) ∧
      ∀ a ,
        v' (mono₀ (R.faceAt j a)) =
          u (mono₀ a) := by
  by_cases hk : 0 < min R.B.card j
  · have hlaw : RespectsSemanticsBelow C.rows (faceIndex R.B j)
        (fun a => u (mono₀ ((R.faceAt j).symm a))) := by
      apply (R.respects_iff _).mpr
      simpa only [Equiv.symm_apply_apply] using hu.mono (faceIndex_le)
    obtain ⟨v', hv', hcap, hface⟩ := C.bountiful.extend (faceIndex_mem R.B_mem hk)
      (effC_mem (hk.trans_le (min_le_right _ _))
        ((hk.trans_le (min_le_left _ _)).trans_le (by exact?)))
      (faceIndex_le) hlaw hv hγ (fun a => by
        grind)
    exact ⟨v', hv', hcap, fun a => by simpa using hface (R.faceAt j a)⟩
  · exact ⟨v, hv, fun _ => rfl, fun a => (faceIndex_absent hk (R.faceAt j a)).elim⟩

