/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedSuccessor
public import VaughtConjecture.Knight.PaddedIteration
public import VaughtConjecture.Knight.PaddedFaceTransport

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedIteration

open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder LowOnlyPaddedContract

open SourcePrefixRows SharpWitnessComposition PairedSlotComparison

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι} {R : Finset (Finset ι)} {m n K : ℕ} {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K} {hroot : I.RootMatches F.root} {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A}

export Padded (successor)

variable (I F hroot hA hB hC)

abbrev build := Padded.build (initial I F hroot hA hB hC)

theorem build_plan (t : ℕ) (ht : t + 2 ≤ A.card) :
    (build I F hroot hA hB hC t ht).carrier.plan = I.boundary.plan :=
  Padded.build_plan _ rfl t ht

/-- The fixed input and LOW family underlying all heights of one padded tower. -/
structure BuildContext {ι : Type*} [DecidableEq ι] (A B C : Finset ι)
    (R : Finset (Finset ι)) (m n K : ℕ) where
  I : WholeDonorBoundary.Input A B C R m n n
  F : LowOnly.Family I.left I.right K
  root : I.RootMatches F.root
  height : 2 ≤ A.card
  leftProper : B ⊂ A
  rightProper : C ⊂ A

namespace BuildContext

variable (L : BuildContext A B C R m n K)

abbrev spec := LowOnlyPaddedContract.spec L.I L.F L.root L.height L.leftProper L.rightProper

abbrev initial := LowOnlyPaddedContract.initial L.I L.F L.root L.height L.leftProper L.rightProper

abbrev tower := Padded.build L.initial

abbrev advance (t : ℕ) (ht : t + 2 ≤ A.card) (r : ℕ) (hr : t + r + 2 ≤ A.card) :=
  Padded.buildEquiv L.initial t ht (A, t + 2) le_rfl r hr

include L in
theorem pos : 0 < A.card := by
  have := L.height
  omega

end BuildContext

end

end VaughtConjecture.Knight.LowOnlyPaddedIteration
