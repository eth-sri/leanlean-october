/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.LowOnlyPaddedInstallation
import VaughtConjecture.Knight.LowOnlyPaddedStepSupply
import VaughtConjecture.Knight.LowOnlyPaddedLiftingReady

/-! # Closed recursive LOW installation endpoints

The actual recursive outputs preserve KVC's checked grade-two lifting ledger.
They also admit native sections, including literal top, at every constructed
height. At full height this supplies a lawful whole display on the coded,
consistent, complete carrier, with both original faces literal. Higher lifting
and the separator readback remain separate; no legal probe is packaged here.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedEndpoints
open     LowOnly 
open LowOnlyPaddedContract LowOnlyPaddedIteration 

noncomputable section
variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n K : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right K)
  (hroot : F.root.Covers I.shared.f I.shared.g)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)


local notation "build₀" => build I F hroot hA hB hC

def original t (ht : t + 2 ≤ A.card) d :=
  (build₀ t ht).baseMap
    (RelativeLadderLayer.old I.boundary (by omega) d)

theorem original_index t (ht : t + 2 ≤ A.card) d :
    (build₀ t ht).carrier.cell (original I F hroot hA hB hC t ht d) =
      I.boundary.cell d :=
  ((build₀ t ht).base_index _).trans
    (RelativeLadderLayer.old_index d)

