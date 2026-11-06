
import VaughtConjecture.Knight.PointwiseLabels
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.CanonicalPairLowerLifting
import VaughtConjecture.Knight.SourcePrefixAmbient

/-! # An active upper layer retaining proper owners of its own grade

The lower pair is constructed over the grade-two cut and spliced with all old
proper owners. The new upper sources are its supported selected sections, at
one fixed outer grid and ceiling. No arbitrary positive continuation of a
lower physical section is required.
-/

namespace VaughtConjecture.Knight.CanonicalProperOwnerLayer


noncomputable section

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}
variable (sem : Semantics D) (k : ℕ) (h2k : 2 < k) (hkA : k ≤ A.card)
variable (hp : AvoidsValue D.scope A) 

abbrev two_le := h2k.le.trans hkA
abbrev one_le := (by decide : 1 ≤ 2).trans (two_le k h2k hkA)
abbrev lowerScheme := CanonicalPairBoundary.scheme sem 1 2 (by decide)
  (one_le k h2k hkA) (by decide) (two_le k h2k hkA)
abbrev lowerSem := CanonicalPairBoundary.rows sem 1 2 (by decide)
  (one_le k h2k hkA) (by decide) (two_le k h2k hkA) hp (by decide)

