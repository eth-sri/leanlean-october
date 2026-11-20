/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.LowOnlyDonorFibre

@[expose] public section

namespace VaughtConjecture.Knight.LowOnly.Family

open Transform Value ExtOrd AmalgamationPlan CappedDonor

noncomputable section

variable {n K : ℕ} {P C : SemScheme n} (F : Family P C K)

def zero : State P C := ⟨fun _ => ⊥, fun _ => ⊥, ⊥⟩

theorem zero_admissible (j : ℕ) : F.Admissible j (zero : State P C) where
  lawfulP := RespectsSemanticsBelow.bot _ _
  lawfulC := RespectsSemanticsBelow.bot _ _
  shared _ := rfl
  futureP _ _ := selfVis_bot _
  futureC _ _ := selfVis_bot _
  cutoff := selfVis_bot _
  low _ h := (not_lt_bot h).elim

end

end VaughtConjecture.Knight.LowOnly.Family
