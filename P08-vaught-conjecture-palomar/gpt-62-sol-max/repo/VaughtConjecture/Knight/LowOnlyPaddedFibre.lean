/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.PaddedNativeFace
public import VaughtConjecture.Knight.LowOnlyPaddedSuccessor
public import VaughtConjecture.Knight.LowOnlySupportedRepair
public import VaughtConjecture.Knight.LowOnlyFibres

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedFibre

open Transform Value ExtOrd Padded CappedDonor LowOnly LowOnlyOrderedLadder LowOnlyPaddedContract

noncomputable section

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  {I : WholeDonorBoundary.Input A B C R m n n} {F : LowOnly.Family I.left I.right K}
  {hroot : I.RootMatches F.root}
  {hA : 2 ≤ A.card} {hB : B ⊂ A} {hC : C ⊂ A}

variable (I F hroot hA hB hC)

theorem privateNative : NativeFace (K := spec I F hroot hA hB hC) I.rightFace (fun j => min j n) where
  le_cutoff _ := min_le_left _ _
  monotone _ _ h := min_le_min_right _ h
  grade_cut d _ h := le_min h (gradeC_le d)
  fibre hj _ := (F.private_fibre hj).reindex (fun _ hs d => (LowOnlyOrderedLadder.field_private I F hroot hs d.1).symm)

theorem donorNative : NativeFace (K := spec I F hroot hA hB hC) I.leftFace (fun j => min j n) where
  le_cutoff _ := min_le_left _ _
  monotone _ _ h := min_le_min_right _ h
  grade_cut d _ h := le_min h (gradeC_le d)
  fibre hj _ := (F.donor_fibre hj).reindex (fun s _ d => (LowOnlyOrderedLadder.field_donor I s d.1).symm)

end

end VaughtConjecture.Knight.LowOnlyPaddedFibre
