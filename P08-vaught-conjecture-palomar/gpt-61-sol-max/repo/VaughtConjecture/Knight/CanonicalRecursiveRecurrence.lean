
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.CanonicalRecursiveBountiful

/-! # Same-contract bountifulness recurrence on the constructed stack

The semantic and selected-section data are the actual recursively constructed
state. Readiness adds consistency of the retained boundary and bountifulness
of the current grade cut. Higher proper owners are retained, not discarded.

Initialization of bountifulness on this exact recursive seed remains explicit.
An unrelated three-grade catalogue equivalence is not used to discharge it.
This is not ordered coatom installation or receiving-family realization.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveRecurrence
section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : AvoidsValue D.scope A)

def Ready m (hm : m + 3 ≤ A.card) :=
  sem.IsConsistent ∧
    (GradeCutBoundary.rows (CanonicalRecursiveContract.carrier sem m hm) (m + 3)
      (CanonicalRecursiveSemantics.rows sem hp m hm)).IsBountiful

variable (hold : CanonicalCoatomBountiful.OldLifts sem) {L R : Finset ι}
variable (hL : L ∈ D.plan) (hR : R ∈ D.plan) (hLA : L ≠ A) (hRA : R ≠ A)
variable (hO : L ∩ R ∈ D.plan)
variable (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)

include hold hL hR hLA hRA hO hcover in
/-- One constructor preserves the identical readiness predicate at the next
grade. All selected-section fields belong to its constructed state. -/
theorem successor n (hA : n + 4 ≤ A.card)
    (hready : Ready sem hp n (Nat.le_of_succ_le hA))
    (hLc : n + 4 ≤ L.card) (hRc : n + 4 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → n + 4 ≤ C.card →
      ∃ d , D.cell d = (C, n + 4)) :
    Ready sem hp (n + 1) hA :=
  ⟨hready.1, CanonicalRecursiveBountiful.bountiful sem n hA hp hready.2 hold
    hL hR hLA hRA hLc hRc hO hcover hcomplete⟩

include hold hL hR hLA hRA hO hcover in
/-- Finite grade iteration, conditional on readiness of the actual seed.
The fixed coatom sizes bound this iteration; it is not arbitrary request or
stage iteration and does not manufacture initial bountifulness. -/
theorem iterate n (hA : n + 3 ≤ A.card)
    (hseed : Ready sem hp 0 (by omega : 3 ≤ A.card))
    (hLc : n + 3 ≤ L.card) (hRc : n + 3 ≤ R.card)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ n + 3 →
      ∃ d , D.cell d = (C, i)) :
    Ready sem hp n hA := by
  induction n with
  | zero => exact hseed
  | succ n ih =>
    have ha  := Nat.le_of_succ_le hA
    have hl  := Nat.le_of_succ_le hLc
    have hr  := Nat.le_of_succ_le hRc
    have hs := ih ha hseed hl hr
      (fun C hC hCA i hi hic hin => hcomplete C hC hCA i hi hic (by omega))
    exact successor sem hp hold hL hR hLA hRA hO hcover n hA hs hLc hRc
      (fun C hC hCA hic => hcomplete C hC hCA (n + 4) (by omega) hic le_rfl)

