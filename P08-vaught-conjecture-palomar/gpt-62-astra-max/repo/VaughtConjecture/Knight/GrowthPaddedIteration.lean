/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GrowthFrame
public import VaughtConjecture.Knight.GrowthPaddedContract

/-! # Iterated actual padded growth rows and incoming renderings

Each successor returns the invariant it consumes. Starting at the unchanged
checked grade-two carrier therefore constructs the actual one-scope rows and
renderings through every available finite height. This is not a bountifulness
or model-receiving theorem. The recursion is specialized from the checked LOW
construction, with separate donor/private arities and growth admission.
-/

@[expose] public section

namespace VaughtConjecture.Knight.GrowthPaddedIteration
open Transform Value ExtOrd Growth GrowthOrderedBase GrowthHigherSources
open GrowthPaddedContract
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n J : ℕ}
  {I : WholeDonorBoundary.Input A B C R m (n + 1) J}
  {X : I.GrowthData}
  {frame : I.GrowthFrame X} {k : ℕ}

variable (frame)

abbrev before (t : ℕ) (ht : t+1 ≤ A.card) := PaddedTower.build (system frame) t ht
abbrev build (t : ℕ) (ht : t+2 ≤ A.card) := before frame (t+1) ht

theorem build_plan t (ht : t+2 ≤ A.card) :
    (build frame t ht).carrier.plan = I.boundary.plan := PaddedTower.build_plan _ _

end
end VaughtConjecture.Knight.GrowthPaddedIteration
