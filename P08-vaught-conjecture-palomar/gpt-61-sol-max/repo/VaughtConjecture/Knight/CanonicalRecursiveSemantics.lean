
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.CanonicalRecursiveSuccessorSections

/-! # Constructed recursive semantics and selected sections

Iteration is over grades on a fixed original proper boundary. All semantic
contract fields are constructed by induction. This is not iteration of legal
attachments: unrestricted recursive bountifulness remains a separate theorem.
-/

namespace VaughtConjecture.Knight.CanonicalRecursiveSemantics

open CanonicalRecursiveContract
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (hp : AvoidsValue D.scope A)

/-- Construct every contract field, starting at the actual recursive seed. -/
def state : (n : ℕ) → (hA : n + 3 ≤ A.card) → State sem n hA
  | 0, hA => seed sem hA hp
  | n + 1, hA => CanonicalRecursiveSuccessorSections.successor sem n hA hp
      (state n (Nat.le_of_succ_le hA))

abbrev rows n (hA : n + 3 ≤ A.card) := (state sem hp n hA).rows

theorem consistent (hs : sem.IsConsistent) {n : ℕ} {hA : n + 3 ≤ A.card} :
    (rows sem hp n hA).IsConsistent := (state sem hp n hA).consistent hs

