/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalCodingSupport
public import VaughtConjecture.Knight.CanonicalRecursiveSemantics

/-! # Coding of every installed recursive source row

Old rows are literal. New rows use the proved orbit support, finite canonical
fields, and coded grids. The statement is uniform in the constructed height.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveCoding
open Transform Value ExtOrd CanonicalCodingSupport
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : D.AvoidsScope A)

theorem successor n (hA : n + 1 ≤ A.card)
    P
    (hc : P.rows.IsCoded) : (CanonicalRecursiveSuccessorRows.rows sem n hA hp P).IsCoded := by
  apply layer (CanonicalRecursiveSuccessorRows.predecessor sem n hA) _
    (n + 1) (Nat.succ_pos n) hA (CanonicalRecursiveSuccessorRows.separation sem n hA hp)
    P.rows _ hc (CanonicalRecursiveSuccessorRows.inherited_row sem n hA hp P)
  intro q d
  let F := CanonicalRecursiveSuccessorRows.data sem n hA hp P
  change IsCodedLabel (n + 1)
    (F.rows.E (CanonicalRecursiveSuccessorRows.controller sem n hA q).1 d)
  rw [F.row_new (CanonicalRecursiveSuccessorRows.controller sem n hA q) d]
  apply supported (fun _ hh => grid (n + 1) _ hh)
    (field (GradeCutBoundary.rows D (n + 1) sem) (n + 1)
      (GradeCutBoundary.toCell D (n + 1)) q)
  exact CanonicalRecursiveSuccessorRows.source_supported sem n hA hp P q d.1

theorem coded (hc : sem.IsCoded) n (hA : n ≤ A.card) :
    (CanonicalRecursiveSemantics.rows sem hp n hA).IsCoded := by
  induction n with
  | zero => exact hc
  | succ n ih =>
    exact successor sem hp n hA
      (CanonicalRecursiveSemantics.state sem hp n (Nat.le_of_succ_le hA))
      (ih (Nat.le_of_succ_le hA))

end
end VaughtConjecture.Knight.CanonicalRecursiveCoding
