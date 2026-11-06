/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyPaddedInstallation
public import VaughtConjecture.Knight.LowOnlyPaddedStepSupply
public import VaughtConjecture.Knight.LowOnlyPaddedLiftingReady

/-! # Closed recursive LOW installation endpoints

The actual recursive outputs preserve KVC's checked grade-two lifting ledger.
They also admit native sections, including literal top, at every constructed
height. At full height this supplies a lawful whole display on the coded,
consistent, complete carrier, with both original faces literal. Higher lifting
and the separator readback remain separate; no legal probe is packaged here.
-/

@[expose] public noncomputable section

namespace VaughtConjecture.Knight.LowOnlyPaddedEndpoints
open Transform Value ExtOrd CappedDonor LowOnly LowOnlyOrderedLadder LowOnlyPaddedContract LowOnlyPaddedIteration LowOnlyPaddedInstallation
open AmalgamationPlan

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : Finset (Finset ι)} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : ∀ i : Cell I.common.scheme,
    ∃ a : I.left.scheme.below (F.root.A, F.root.A.card),
      a.1 = I.shared.f i ∧ (F.root.face a).1 = I.shared.g i)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

def original (t : ℕ) (ht : t + 2 ≤ A.card) (d : Cell I.boundary) :
    Cell (build I F hroot hA hB hC t ht).carrier :=
  (build I F hroot hA hB hC t ht).baseMap
    (RelativeLadderLayer.old I.boundary (by omega) d)

theorem original_index (t : ℕ) (ht : t + 2 ≤ A.card) (d : Cell I.boundary) :
    (build I F hroot hA hB hC t ht).carrier.cell (original I F hroot hA hB hC t ht d) =
      I.boundary.cell d :=
  ((build I F hroot hA hB hC t ht).base_index _).trans
    (RelativeLadderLayer.old_index I.boundary (by omega) d)
