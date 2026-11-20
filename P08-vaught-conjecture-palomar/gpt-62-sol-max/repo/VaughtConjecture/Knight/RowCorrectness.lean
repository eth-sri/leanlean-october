/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.Transform
public import VaughtConjecture.Knight.VisibilityAlgebra

@[expose] public section

namespace VaughtConjecture.Knight

open Transform Value ExtOrd

/-- `min` distributes over a monotone shifter. -/
theorem monotone_min_apply {σ : ExtOrd → ExtOrd} (hσ : Monotone σ) (a b : ExtOrd) :
    σ (min a b) = min (σ a) (σ b) := by
  rcases le_total a b with h | h
  all_goals aesop

end VaughtConjecture.Knight
