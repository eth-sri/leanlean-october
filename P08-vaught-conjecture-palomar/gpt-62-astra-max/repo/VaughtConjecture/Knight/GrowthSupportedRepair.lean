/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthNormalization
public import VaughtConjecture.Knight.CappedDonorCatalogue

/-! # Supported growth catalogue insertion

The terminal-block and protected-grid calculations are adapted from
`LowOnlyTerminalSupport` and `LowOnlySupportedRepair`; their admission step is
the independently proved growth `Admitted.map`, not the LOW fibre. Top-valued
inputs are first capped above the entire protected prefix, then the whole fresh
terminal block is collapsed. No physical renderer lawfulness is assumed or claimed.
-/

@[expose] public section

namespace VaughtConjecture.Knight.Growth
open Transform Value ExtOrd AmalgamationPlan CappedDonor CappedDonor.Ref
open CanonicalPairedInverse
noncomputable section
variable {ιA ιQ : Type*} [DecidableEq ιA] [DecidableEq ιQ]
  {A : Finset ιA} {Q : Finset ιQ} {DA : CellScheme A} {DQ : CellScheme Q}
  {semA : Semantics DA} {semQ : Semantics DQ}
  {j B : ℕ}

variable (X : RelativeData DA semA DQ semQ)

abbrev ProtectedRepair (a : Field DA DQ → ExtOrd) (s : State DA DQ) (j B : ℕ) := ProfileCatalogue.Repair (profileFamily X j) a s B
end
end VaughtConjecture.Knight.Growth
