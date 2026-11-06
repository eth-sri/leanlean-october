/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

import VaughtConjecture.Knight.BlockStages
import Mathlib.SetTheory.Ordinal.Basic
import VaughtConjecture.Approximation.Prolongation
import VaughtConjecture.Knight.ProlongationNormalization
import VaughtConjecture.Knight.ReductModel

/-! # Knight's stopping rank along the canonical block levels

The Knight façade of `Approximation/Rank.lean` (issue #70): the generic intrinsic
prolongability-through-a-block predicate and stopping rank, instantiated at

* the tower `knightTower` over the limit stages;
* the target class `C := IsModel` (Def. 3.2.1; `KnightRealization.IsModelClass`) — the rank
  measures **certified** prolongation through actual models (`ProlongsToIn IsModel`,
  `ProlongsToClassIn IsModel`, #111), never raw `ProlongsTo`;
* the schedule `blockStage ξ := ⟨blockLevel ξ, _⟩ : LimitStage`, the canonical block levels
  `ω + ω·ξ` of `Knight/Value.lean` (monotone — indeed strictly — by `blockLevel_strictMono`).

Reduct-closure of the target class is the strict model-reduction theorem `IsModel.reduct`
(#101/#112, `Knight/ReductModel.lean`), proved for arbitrary models, so downward closure of
`KnightRealization.ProlongsThroughBlock` is **unconditional** (`prolongsThroughBlock_mono`) —
no receipt, no selected history.

**Endpoint convention** (the `ξ = 0` sanity lemma `prolongsThroughBlock_zero_iff`,
`not_prolongsThroughBlock_zero_iff`): block `ξ` has *terminal level* `blockLevel ξ` and *failed
target* `blockLevel (ξ + 1) = blockLevel ξ + ω`; sources are models of `S^ω`, i.e. live at
`blockStage 0` (`blockStage_zero : blockStage 0 = ⟨ω, _⟩`), and
`¬ ProlongsThroughBlock R 0 ↔ NoProlongationToIn IsModel (blockStage 0 ≤ blockStage 1)` — from
`ω` to `ω + ω` (`blockStage_one_toOrdinal`) — is Knight-VC's `FailsAtAlphaOmega` at `α = ω`.

**Guard.**  `stopRank` is `sInf` of the failure set, so `sInf ∅ = 0`: it is a genuine first
failed block only under `HasFailure` (`stopRank_mem`, `prolongsThroughBlock_iff_lt_stopRank`,
`stopRank_eq_zero_iff`).  `HasFailure` is **termination** (a failure exists); the counting
kernel additionally needs `stopRank R < ω₁` (totality).  That every model of `S^ω` has a
countable failure — both facts — is the theorem of the history / linked-stop layer (#30/#31),
not assumed here.
`stopLevel R := blockLevel (stopRank R)` is the *terminal* level of the stopping block
(TERMINOLOGY: stopping index / stopping level), not the failed target. -/

namespace VaughtConjecture.Knight


universe w

namespace KnightRealization

theorem isModelClass_reduct {δ δ' : LimitStage} (h : δ ≤ δ') {N : Type w}
    (R' : KnightRealization δ' N) (hR' : IsModelClass R') : IsModelClass (R'.reduct h) :=
  hR'.reduct h

/-! ### Prolongation through a block -/

/-! ### The stopping rank -/

/-! ### Isomorphism invariance and the class rank -/


