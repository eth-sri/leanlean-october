/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthHigherSources

/-! # Protected decoding on the actual padded growth successor

Both physical source sections are constructed lawfully by the successor.
The protected inverse then retains every actual coordinate at the native cut,
including unused rungs and long tips. Its decoded output is lawful without a
shortness assumption on the inherited rows.

The two source-repair corollaries accept a lawful original-face prescription
at this native cut. They are not arbitrary-ambient lifting: constructing that
prescription from an external physical chart, and restoring above an owner,
are separate obligations. Adapted from `LowOnlyPaddedDecode`, consuming the
actual growth fibres rather than substituting LOW.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedDecode
open Transform Value ExtOrd CappedDonor Growth CanonicalPairedInverse
open GrowthOrderedBase
noncomputable section

section Grid
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  {X : RelativeData DA semA DQ semQ} {j b : ℕ}
  {a : Field DA DQ → ExtOrd} {S : State DA DQ}

/-- The replacement indexes the existing fixed catalogue. -/
def repairAnchor (r : ProtectedRepair X a S j b) : Catalogue X j :=
  r.member _

end Grid

end
end VaughtConjecture.Knight.GrowthPaddedDecode
