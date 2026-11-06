/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import Mathlib.Tactic

import VaughtConjecture.Knight.LowOnlyPaddedStepChart
import VaughtConjecture.Knight.LowSeparatorPaired

/-! # Paired-separator readback on the unchanged grade-two seed

The grade-two installer has weighted-source rows with an empty weighted-node
type. Its actual leaf equations supply the same paired readback as the higher
recursive steps. The strict physical separator remains an explicit premise.
-/

namespace VaughtConjecture.Knight.LowOnlyPaddedTwoReadback
open     LowOnly 
open LowOnlyPaddedSuccessor  

variable {ι : Type*} [DecidableEq ι] {A B C : Finset ι}
  {R : VaughtConjecture.AmalgamationPlan.SupportFamily ι} {m n : ℕ}
  (I : WholeDonorBoundary.Input A B C R m n n) (F : LowOnly.Family I.left I.right 2)
  (hroot : F.root.Covers I.shared.f I.shared.g)
  (hA : 2 ≤ A.card) (hB : B ⊂ A) (hC : C ⊂ A)

theorem exists_top_chart {q}
    (hq : RespectsSemanticsBelow (rows I F hroot hA hB hC) (A, 2) q)
    (htop : ∃ d, (carrier I F hroot hA hB hC).grade d.1 = 2 ∧ q d = ⊤) :
    ∃ a , ∃ σ ,
      Witness (gTop 2) σ ∧ ∀ d, σ (source I F hroot hA hB hC a d.1) = q d := by
  obtain ⟨a, σ, M, hσ, hM, hread⟩ := LowOnlyPaddedCharts.exists_chart I F hroot hA hB hC hq
  obtain ⟨d, hd, htop⟩ := htop
  have hMt  := top_le_iff.mp (htop ▸ hM d hd)
  exact ⟨a, σ, hσ, fun d => (hread d).trans (by rw [hMt, min_top_right])⟩


