/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TopGradeStableCore

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower StageType KnightRealization Value ExtOrd

universe w

variable {M : Type w} {α : LimitStage} {R : KnightRealization α M}

/-- A constant tail above every context bounds the top grade of every context. -/
theorem topGrade_le_of_isCoinitial {K : ℕ}
    (hcoin : KnightRealization.IsCoinitial {x : R.LabelledExt | x.type.topGrade = K})
    (x : R.LabelledExt) : x.type.topGrade ≤ K := by
  obtain ⟨y, hxy, hy⟩ := hcoin x
  exact (LabelledExt.topGrade_mono hxy).trans_eq (hy (le_refl y))

end VaughtConjecture.Knight
