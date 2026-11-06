/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorOrdinarySections
public import VaughtConjecture.Knight.CanonicalRecursiveFace
public import VaughtConjecture.Knight.CanonicalRecursiveInitialized
public import VaughtConjecture.Knight.CanonicalRecursiveCoding

/-! # Ordinary scope lifting from the actual legal input faces

Derive the semantic inputs to the grade recurrence from two compatible legal
schemes, on the same rows used by `WholeDonorOrdinarySections`. In the two-facet
case this gives unrestricted lifting through the constructed height, not an
existential replacement carrier. It does not yet iterate over missing scopes.
-/

@[expose] public section

set_option autoImplicit false
namespace VaughtConjecture.Knight.WholeDonorOrdinaryLift
open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension
open WholeDonorOrdinarySections
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}
variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)
variable (hBA : B ≠ A) (hCA : C ≠ A)

theorem left_mem : B ∈ I.boundary.plan :=
  I.leftPlan_le I.leftScheme.isPlan.domain_mem

theorem right_mem : C ∈ I.boundary.plan :=
  I.rightPlan_le I.rightScheme.isPlan.domain_mem

variable (n : ℕ) (hA : n + 3 ≤ A.card)


variable {CI BJ : Finset ι × ℕ}

variable (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)

end
end VaughtConjecture.Knight.WholeDonorOrdinaryLift
