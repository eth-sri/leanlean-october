/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedPairLift
public import VaughtConjecture.Knight.LowOnlyPaddedRendering
public import VaughtConjecture.Knight.TargetGradeLifting

/-! # Checked lower lifting and incoming rendering on the same padded carrier

The renderer is ported unchanged from integration commit
49f4d94eb2b5fca4a0232e3f96a80f629441b109. Both the lifting invariant and the
incoming semantic contract are now proved on its actual predecessor, not
fields of an assumed successor record. No grade-three layer is installed here.
-/

@[expose] public section

namespace VaughtConjecture.Knight.LowOnlyPaddedLiftingReady
open Transform Value ExtOrd CappedDonor LowOnly AmalgamationPlan
open LowOnlyPaddedSuccessor LowOnlyPaddedRendering
noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)
  (hcover : ∀ S ∈ R, S ≠ A → S ⊆ B ∨ S ⊆ C)

include hcover

theorem through_two : TargetGradeLifting.Through (rows I F hroot hA hB hC) 2 :=
  fun hU hV h hj => LowOnlyPaddedPairLift.lift I F hroot hA hB hC hcover hU hV h hj

end
end VaughtConjecture.Knight.LowOnlyPaddedLiftingReady
