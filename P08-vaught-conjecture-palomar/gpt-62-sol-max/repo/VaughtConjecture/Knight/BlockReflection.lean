/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.ExpansionUniqueness

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

/-- The next `ω`-block of a limit stage. -/
noncomputable def LimitStage.nextBlock (α : LimitStage) : LimitStage :=
  ⟨α.1 + Ordinal.omega0, Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0⟩

theorem LimitStage.le_nextBlock (α : LimitStage) : α ≤ α.nextBlock :=
  show α.1 ≤ α.1 + Ordinal.omega0 from le_add_of_nonneg_right zero_le

end VaughtConjecture.Knight
