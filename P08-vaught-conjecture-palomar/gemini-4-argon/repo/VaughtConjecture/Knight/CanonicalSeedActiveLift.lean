/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CanonicalSeedOwnerLift
public import VaughtConjecture.Knight.CanonicalSeedRestoration

/-! # Literal active-owner lifting on the recursive seed

The prescription and ambient are arbitrary lawful physical sections. A maximal
prescribed owner is constructed by availability. Old-face lifting constructs
the coded boundary repair; predecessor bountifulness restores the complete
lower prescription, including distinct values above the owner and literal top.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.CanonicalSeedActiveLift
open Transform Value ExtOrd CoatomBoundaryExtension CanonicalRecursiveSeedRows CanonicalSeedCutPrefix

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
  (sem : Semantics D) (hA : 3 ≤ A.card)
  (hp : ∀ d : Cell D, D.scope d ≠ A)

abbrev outputRows := rows sem hA hp
