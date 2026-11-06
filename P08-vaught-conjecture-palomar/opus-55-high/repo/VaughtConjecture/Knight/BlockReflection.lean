/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.ReductModel
public import VaughtConjecture.Knight.ExpansionUniqueness

/-! # Old-block requests reflect through reduction; the next block

Reduction to the source stage fixes every proper label and sends every label at or above the
source stage to `∞` (`truncExt`).  Consequently membership in each of the four old-block
request families — a generalized-saturation domain, a prescribed `−∞`-pattern, an old
uniformity band, an old high-grade threshold — **reflects** from the reduct to the type
(`mem_*_of_reduceType_mem`): a target label whose reduct witnesses the request witnesses it
itself.  This is what lets a next-block realization discharge the four old model clauses by
exhibiting source witnesses (its reduct being literally the source).

In the block `[α, α + ω)` itself, the only new non-successor uniformity index is `α`
(`nonSuccessor_lt_add_omega_old_or_base`), and the natural ladder `α + (k+1)` is cofinal
among the new high-grade thresholds (`lt_add_nat_succ_of_lt_add_omega`).

`LimitStage.nextBlock` packages `α + ω` as a limit stage.  (Reviewer kernels, 2026-08-30.) -/

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value ExtOrd

universe w

section
variable (α : LimitStage)

/-- The next `ω`-block of a limit stage. -/
noncomputable def LimitStage.nextBlock  : LimitStage :=
  ⟨α.1 + Ordinal.omega0, Ordinal.isSuccLimit_add _ Ordinal.isSuccLimit_omega0⟩

theorem LimitStage.le_nextBlock  : α ≤ α.nextBlock :=
  show α.1 ≤ α.1 + Ordinal.omega0 from le_add_of_nonneg_right zero_le

end

end VaughtConjecture.Knight
