import PalomarProof.Ordinal
/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.Tower

/-! # The block schedule, without stopping-rank machinery

Elementary stage arithmetic used by both receiving and the later rank analysis. -/

namespace VaughtConjecture.Knight

open  Value

/-! ### The canonical block schedule -/

/-- The canonical block levels as limit stages: `blockStage ξ := ⟨blockLevel ξ, _⟩` with
`blockLevel ξ = ω + ω·ξ` (`Knight/Value.lean`).  The stage schedule of the Knight stopping rank:
block `ξ` runs from its terminal level `blockStage ξ` to its failed target `blockStage (ξ + 1)`. -/
noncomputable def blockStage (ξ : Ordinal₀) : LimitStage :=
  ⟨blockLevel ξ, isSuccLimit_blockLevel ξ⟩

@[simp] theorem blockStage_toOrdinal ξ :
    (blockStage ξ).toOrdinal = blockLevel ξ := rfl

theorem blockStage_strictMono : StrictMono blockStage :=
  fun _ _ h => Subtype.mk_lt_mk.mpr (blockLevel_strictMono h)

def blockStage_mono := blockStage_strictMono.monotone

/-- The base stage is `ω`: sources of the Knight rank are models of `S^ω`. -/
theorem blockStage_zero : blockStage 0 = ⟨Ordinal.omega0, Ordinal.isSuccLimit_omega0⟩ :=
  Subtype.ext blockLevel_zero

/-- The failed target of block `ξ` is one `ω`-block above its terminal level. -/
theorem blockStage_succ_toOrdinal ξ :
    (blockStage (ξ + 1)).toOrdinal = blockLevel ξ + Ordinal.omega0 := by
  rw [blockStage_toOrdinal, ← Order.succ_eq_add_one, blockLevel_succ]

namespace KnightRealization

/-- The base-source stage bound. -/
def blockStage_zero_le ξ :=
  blockStage_mono (zero_le : (0 : Ordinal₀) ≤ ξ)

/-- Terminal stage to failed target of the same block. -/
def blockStage_le_succ {ξ : Ordinal₀} :=
  blockStage_mono (le_self_add : ξ ≤ ξ + 1)


