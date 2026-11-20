/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedCoding
public import VaughtConjecture.Knight.CoatomRecursiveInput

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveCoding

open Transform Value ExtOrd CanonicalCodingSupport

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)

theorem successor (n : ℕ) (hA : n + 3 ≤ A.card)
    (P : CanonicalRecursiveContract.Stage sem n (Nat.le_of_succ_le hA))
    (hc : P.rows.IsCoded) : (CanonicalRecursiveSuccessorRows.rows (⟨hp, P⟩ : CanonicalRecursiveContract.Step sem n hA)).IsCoded := by
  apply layer (CanonicalRecursiveSuccessorRows.predecessor sem n hA) _
    (n + 3) (Nat.succ_pos (n + 2)) hA (CanonicalRecursiveSuccessorRows.separation sem n hA hp)
    P.rows _ hc (CanonicalRecursiveSuccessorRows.inherited_row (⟨hp, P⟩ : CanonicalRecursiveContract.Step sem n hA))
  intro q d
  let F := CanonicalRecursiveSuccessorRows.data (⟨hp, P⟩ : CanonicalRecursiveContract.Step sem n hA)
  change IsCodedLabel (n + 3)
    (F.rows.E (CanonicalRecursiveSuccessorRows.controller sem n hA q).1 d)
  rw [F.row_new (CanonicalRecursiveSuccessorRows.controller sem n hA q) d]
  apply supported (fun _ hh => grid (n + 3) _ hh)
    (field (GradeCutBoundary.rows D (n + 3) sem) (n + 3)
      (GradeCutBoundary.toCell D (n + 3)) q)
  exact CanonicalRecursiveSuccessorRows.source_supported (⟨hp, P⟩ : CanonicalRecursiveContract.Step sem n hA) q d.1

private theorem stage_coded (hc : sem.IsCoded) (n : ℕ) (hA : n + 2 ≤ A.card) :
    (CanonicalRecursiveSemantics.stage sem hp n hA).rows.IsCoded := by
  induction n with
  | zero => exact CanonicalSeedCoding.pair sem hA hp hc
  | succ n ih =>
    exact successor sem hp n hA
      (CanonicalRecursiveSemantics.stage sem hp n (Nat.le_of_succ_le hA))
      (ih (Nat.le_of_succ_le hA))

theorem coded (hc : sem.IsCoded) (n : ℕ) (hA : n + 3 ≤ A.card) :
    (CanonicalRecursiveSemantics.rows sem hp n hA).IsCoded :=
  stage_coded sem hp hc (n + 1) hA

/-- The old coding premise comes from the two legal input schemes. -/
theorem coatom {s : AmalgamatedBoundaryPlan.Step A} {m n : ℕ}
    (I : SemSchemeBoundaryInput.Input s m (n + 3) (n + 3)) :
    (CoatomRecursiveInput.rows I).IsCoded :=
  coded I.rows I.proper I.coded n (CoatomRecursiveInput.height_le I)

end

end VaughtConjecture.Knight.CanonicalRecursiveCoding
