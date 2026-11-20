/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowFrame
public import VaughtConjecture.Knight.LowOnlyPaddedContract

/-! # Iterated actual padded LOW rows and incoming renderings

Each successor returns the invariant it consumes. Starting at the unchanged
checked grade-two carrier therefore constructs the actual one-scope rows and
renderings through every available finite height. This is not a bountifulness
or model-receiving theorem.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedIteration
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder LowOnlyPaddedContract
open SourcePrefixRows SharpWitnessComposition PairedSlotComparison
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {frame : I.LowFrame F} {k : ℕ}

variable (frame)

abbrev before (t : ℕ) (ht : t+1 ≤ A.card) := PaddedTower.build (system frame) t ht
abbrev build (t : ℕ) (ht : t+2 ≤ A.card) := before frame (t+1) ht

theorem build_plan (t : ℕ) (ht : t+2 ≤ A.card) :
    (build frame t ht).carrier.plan = I.boundary.plan := PaddedTower.build_plan _ _

theorem build_consistent (t : ℕ) (ht : t + 2 ≤ A.card) :
    (build frame t ht).rows.IsConsistent :=
  (build frame t ht).consistent

end
end VaughtConjecture.Knight.LowOnlyPaddedIteration
