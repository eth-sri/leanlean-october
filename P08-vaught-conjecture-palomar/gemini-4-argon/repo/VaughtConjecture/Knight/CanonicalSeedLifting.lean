/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.FullScopeBountiful
public import VaughtConjecture.Knight.GradeCutLifting

/-! # Recursive lifting: inherited targets and vertical pasting

Inherited lifting is transported by actual row and occurrence equations, not
catalogue equivalence. Vertical pasting retains the original upper-visible
cap and requires no bountifulness of the new output.
The active new-grade proper-face lift is not asserted here.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalSeedLifting
open Transform Value ExtOrd CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 3 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)
open CanonicalRecursiveSeedRows CanonicalRecursiveSeedSections

/-- Every target omitting the new controller index transports its full
single-face lifting clause from the actual predecessor semantics. -/
theorem lower_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ 2)
    (hb : CappedLift (predecessorRows sem hA hp) h) : CappedLift (rows sem hA hp) h :=
  have hJ' : ¬ GradedLe (A, 3) J := fun he => by have := he.2; omega
  have hI' : ¬ GradedLe (A, 3) I := fun hi => hJ' (hi.trans h)
  hb.of_respects_iff (equiv sem hA I hI') (equiv sem hA J hJ') (fun _ => rfl)
    (respects_iff sem hA hp I hI') (respects_iff sem hA hp J hJ')

/-- Actual lower-pair bountifulness comes from the banked two-grade theorem
through its proved row transport, not from a catalogue identification. -/
theorem predecessor_bountiful (hold : CanonicalCoatomBountiful.OldLifts sem)
    {L R : Finset ι} (hL : L ∈ D.plan) (hR : R ∈ D.plan)
    (hLA : L ≠ A) (hRA : R ≠ A) (hLc : 2 ≤ L.card) (hRc : 2 ≤ R.card)
    (hO : L ∩ R ∈ D.plan)
    (hcover : ∀ C ∈ D.plan, C ≠ A → C ⊆ L ∨ C ⊆ R)
    (hcomplete : ∀ C ∈ D.plan, C ≠ A → ∀ i, 0 < i → i ≤ C.card → i ≤ 2 →
      ∃ d : Cell D, D.cell d = (C, i)) :
    (GradeCutBoundary.rows (predecessor sem hA) 2 (predecessorRows sem hA hp)).IsBountiful := by
  apply EffectiveGradeLifting.bountiful_of_bounded_same_grade
    (GradeCutBoundary.grade_bound (predecessor sem hA) 2) (by decide)
  intro C B i hC hB hi hCB
  apply (GradeCutLifting.lift_iff (predecessorRows sem hA hp) 2 _ hi).mpr
  exact CanonicalPairLowerLifting.lower_lift sem hp (two_le hA)
    hold hL hR hLA hRA hLc hRc hO hcover hcomplete hC hB ⟨hCB, le_rfl⟩ hi
