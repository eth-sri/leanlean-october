/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedCoding
public import VaughtConjecture.Knight.CoatomRecursiveInput

/-! # Coding of every installed recursive source row

Old rows are literal. New rows use the proved orbit support, finite canonical
fields, and coded grids. The statement is uniform in the constructed height.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveCoding
open Transform Value ExtOrd CanonicalCodingSupport
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)

theorem successor (m : ℕ) (hA : m + 3 ≤ A.card)
    (P : CanonicalRecursiveContract.StateAt sem m (Nat.le_of_succ_le hA))
    (hc : P.rows.IsCoded) :
    (CanonicalRecursiveSemantics.stepRows sem m hA hp P).IsCoded := by
  apply layer (CanonicalRecursiveSemantics.predecessor sem m hA) _
    (m + 3) (Nat.succ_pos (m + 2)) hA (CanonicalRecursiveSemantics.separation sem m hA hp)
    P.rows _ hc (CanonicalRecursiveSemantics.inherited_row sem m hA hp P)
  intro q d
  let F := CanonicalRecursiveSemantics.data sem m hA hp P
  change IsCodedLabel (m + 3)
    (F.rows.E (CanonicalRecursiveSemantics.controller sem m hA q).1 d)
  rw [F.row_new (CanonicalRecursiveSemantics.controller sem m hA q) d]
  apply supported (fun _ hh => grid (m + 3) _ hh)
    (field (GradeCutBoundary.rows D (m + 3) sem) (m + 3)
      (GradeCutBoundary.toCell D (m + 3)) q)
  exact CanonicalRecursiveSemantics.source_supported sem m hA hp P q d.1

theorem codedAt (hc : sem.IsCoded) (m : ℕ) (hA : m + 2 ≤ A.card) :
    (CanonicalRecursiveSemantics.rowsAt sem hp m hA).IsCoded := by
  induction m with
  | zero => exact CanonicalSeedCoding.pair sem hA hp hc
  | succ m ih =>
    exact successor sem hp m hA
      (CanonicalRecursiveSemantics.stateAt sem hp m (Nat.le_of_succ_le hA))
      (ih (Nat.le_of_succ_le hA))

theorem coded (hc : sem.IsCoded) (n : ℕ) (hA : n + 3 ≤ A.card) :
    (CanonicalRecursiveSemantics.rows sem hp n hA).IsCoded :=
  codedAt sem hp hc (n + 1) hA

/-- The old coding premise comes from the two legal input schemes. -/
theorem coatom {s : AmalgamatedBoundaryPlan.Step A} {m n : ℕ}
    (I : SemSchemeBoundaryInput.Input s m (n + 3) (n + 3)) :
    (CoatomRecursiveInput.rows I).IsCoded :=
  coded I.rows I.proper I.coded n (CoatomRecursiveInput.height_le I)

end
end VaughtConjecture.Knight.CanonicalRecursiveCoding
