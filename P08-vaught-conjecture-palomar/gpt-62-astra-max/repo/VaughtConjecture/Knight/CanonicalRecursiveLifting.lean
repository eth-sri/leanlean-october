/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics

/-! # Recursive lifting: inherited targets and vertical pasting

Inherited lifting is transported by actual row and occurrence equations, not
catalogue equivalence. Vertical pasting retains the original upper-visible
cap and requires no bountifulness of the new output.
The active new-grade proper-face lift is not asserted here.
-/

@[expose] public section

namespace VaughtConjecture.Knight.CanonicalRecursiveLifting
open Transform Value ExtOrd CoatomBoundaryExtension
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (n : ℕ) (hA : n + 1 ≤ A.card)
variable (hp : D.AvoidsScope A)
variable (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
open CanonicalRecursiveSuccessorRows CanonicalRecursiveSuccessorSections

/-- Every target omitting the new controller index transports its full
single-face lifting clause from the actual predecessor semantics. -/
theorem inherited_lift {I J : Finset ι × ℕ} (h : GradedLe I J)
    (hJ : ¬ GradedLe (A, n + 1) J) (hb : CappedLift P.rows h) :
    CappedLift (rows sem n hA hp P) h :=
  HighLayerBountiful.transport_lift _ _ _ (Nat.succ_pos n) hA (separation sem n hA hp) P.rows _
    (inherited_row sem n hA hp P) h hJ hb

theorem lower_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ n)
    (hb : CappedLift P.rows h) : CappedLift (rows sem n hA hp P) h :=
  inherited_lift sem n hA hp P h (fun he => by have := he.2; omega) hb

end
end VaughtConjecture.Knight.CanonicalRecursiveLifting
