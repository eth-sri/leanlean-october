/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveBoundaryTransport

/-! # Literal boundary rows on the recursive inventory -/
@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveLiteralRows
open Transform Value ExtOrd CanonicalRecursiveContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : D.AvoidsScope A)

theorem row n (hA : n ≤ A.card) c d :
    (CanonicalRecursiveSemantics.rows sem hp n hA).E (boundary sem n hA c)
      ⟨boundary sem n hA d.1, by
        rw [CanonicalRecursiveInventory.boundary_cell, CanonicalRecursiveInventory.boundary_cell]
        exact d.2⟩ = sem.E c d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let hn := Nat.le_of_succ_le hA
    let c' := boundary sem n hn c
    let d' : (carrier sem n hn).RowDomain c' :=
      ⟨boundary sem n hn d.1, by
        rw [CanonicalRecursiveInventory.boundary_cell, CanonicalRecursiveInventory.boundary_cell]
        exact d.2⟩
    exact (CanonicalRecursiveSuccessorRows.inherited_row sem n hA hp
      (CanonicalRecursiveSemantics.state sem hp n hn) c' d').trans (ih hn)

end
end VaughtConjecture.Knight.CanonicalRecursiveLiteralRows
