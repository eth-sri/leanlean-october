/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveSemantics
public import VaughtConjecture.Knight.FullScopeBountiful

/-! # Recursive lifting: inherited targets and vertical pasting

Inherited lifting is transported by actual row and occurrence equations, not
catalogue equivalence. Vertical pasting retains the original upper-visible
cap and requires no bountifulness of the new output.
The active new-grade proper-face lift is not asserted here.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveLifting
open Transform Value ExtOrd CoatomBoundaryExtension

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)
  (P : CanonicalRecursiveContract.State sem n (Nat.le_of_succ_le hA))
open CanonicalRecursiveSuccessorRows CanonicalRecursiveSuccessorSections

/-- Every target omitting the new controller index transports its full
single-face lifting clause from the actual predecessor semantics. -/
theorem lower_lift {I J : Finset ι × ℕ} (h : GradedLe I J) (hJ : J.2 ≤ n + 3)
    (hb : CappedLift P.rows h) : CappedLift (rows sem n hA hp P) h :=
  have hJ' : ¬ GradedLe (A, n + 4) J := fun he => by have := he.2; omega
  have hI' : ¬ GradedLe (A, n + 4) I := fun hi => hJ' (hi.trans h)
  hb.of_respects_iff (equiv sem n hA I hI') (equiv sem n hA J hJ') (fun _ => rfl)
    (respects_iff sem n hA hp P I hI') (respects_iff sem n hA hp P J hJ')

