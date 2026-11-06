/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.WholeDonorOrdinarySections
import VaughtConjecture.Knight.CanonicalRecursiveFace
import VaughtConjecture.Knight.CanonicalRecursiveInitialized
import VaughtConjecture.Knight.CanonicalRecursiveCoding

/-! # Ordinary scope lifting from the actual legal input faces

Derive the semantic inputs to the grade recurrence from two compatible legal
schemes, on the same rows used by `WholeDonorOrdinarySections`. In the two-facet
case this gives unrestricted lifting through the constructed height, not an
existential replacement carrier. It does not yet iterate over missing scopes.
-/

namespace VaughtConjecture.Knight.WholeDonorOrdinaryLift
section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι}
variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)
theorem left_mem : B ∈ I.boundary.plan :=
  I.leftPlan_le I.leftScheme.isPlan.domain_mem

theorem right_mem : C ∈ I.boundary.plan :=
  I.rightPlan_le I.rightScheme.isPlan.domain_mem

