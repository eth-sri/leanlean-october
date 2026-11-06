/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalRecursiveOwnerLift
public import VaughtConjecture.Knight.CanonicalRecursiveRestoration

/-! # Literal active-owner lifting on the recursive successor

The prescription and ambient are arbitrary lawful physical sections. A maximal
prescribed owner is constructed by availability. Old-face lifting constructs
the coded boundary repair; predecessor bountifulness restores the complete
lower prescription, including distinct values above the owner and literal top.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalRecursiveActiveLift
open Transform Value ExtOrd CoatomBoundaryExtension CanonicalRecursiveSuccessorRows CanonicalRecursiveCutPrefix

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (n : ℕ) (hA : n + 4 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev predecessorState := CanonicalRecursiveSemantics.state sem hp n (Nat.le_of_succ_le hA)
abbrev outputRows := rows sem n hA hp (predecessorState sem n hA hp)
