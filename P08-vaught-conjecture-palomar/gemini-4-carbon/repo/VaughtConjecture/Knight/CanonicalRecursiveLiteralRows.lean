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
variable (sem : Semantics D) (hp : ∀ d : Cell D, D.scope d ≠ A)

theorem rowAt (m : ℕ) (hA : m + 2 ≤ A.card) (c : Cell D) (d : D.below (D.cell c)) :
    (CanonicalRecursiveSemantics.rowsAt sem hp m hA).E (boundaryAt sem m hA c)
      ⟨boundaryAt sem m hA d.1, by
        rw [CanonicalRecursiveInventory.boundary_cell, CanonicalRecursiveInventory.boundary_cell]
        exact d.2⟩ = sem.E c d := by
  induction m with
  | zero =>
    exact GradeCutPairRows.old_row D _ _ 1 2 (by decide)
      (CanonicalPairLocalSections.one_le hA) (by decide) hA hp (by decide)
      sem (CanonicalPairLocalSections.smallRows sem hA hp) c d
  | succ m ih =>
    let hm := Nat.le_of_succ_le hA
    let c' := boundaryAt sem m hm c
    let d' : (carrierAt sem m hm).below ((carrierAt sem m hm).cell c') :=
      ⟨boundaryAt sem m hm d.1, by
        rw [CanonicalRecursiveInventory.boundary_cell, CanonicalRecursiveInventory.boundary_cell]
        exact d.2⟩
    exact (CanonicalRecursiveSemantics.inherited_row sem m hA hp
      (CanonicalRecursiveSemantics.stateAt sem hp m hm) c' d').trans (ih hm)

theorem row (n : ℕ) (hA : n + 3 ≤ A.card) (c : Cell D) (d : D.below (D.cell c)) :
    (CanonicalRecursiveSemantics.rows sem hp n hA).E (boundary sem n hA c)
      ⟨boundary sem n hA d.1, by
        rw [CanonicalRecursiveInventory.boundary_cell, CanonicalRecursiveInventory.boundary_cell]
        exact d.2⟩ = sem.E c d :=
  rowAt sem hp (n + 1) hA c d

end
end VaughtConjecture.Knight.CanonicalRecursiveLiteralRows
