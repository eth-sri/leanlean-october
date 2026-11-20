/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.WholeDonorBoundary
public import VaughtConjecture.Knight.CanonicalRecursiveFace
public import VaughtConjecture.Knight.CanonicalRecursiveInitialized
public import VaughtConjecture.Knight.CanonicalRecursiveCoding

@[expose] public section

namespace VaughtConjecture.Knight.WholeDonorOrdinaryLift

open AmalgamationPlan Transform Value ExtOrd CoatomBoundaryExtension


noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)}

variable {m nL nR : ℕ} (I : WholeDonorBoundary.Input A B C R m nL nR)

theorem left_mem : B ∈ I.boundary.plan :=
  I.leftPlan_le I.leftScheme.isPlan.domain_mem

theorem right_mem : C ∈ I.boundary.plan :=
  I.rightPlan_le I.rightScheme.isPlan.domain_mem

end

end VaughtConjecture.Knight.WholeDonorOrdinaryLift
