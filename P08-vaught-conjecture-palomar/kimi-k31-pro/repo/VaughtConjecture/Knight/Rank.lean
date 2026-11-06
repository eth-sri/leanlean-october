/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.BlockStages
public import VaughtConjecture.Approximation.Rank
public import VaughtConjecture.Knight.ProlongationNormalization
public import VaughtConjecture.Knight.ReductModel

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

@[expose] public section

namespace VaughtConjecture.Knight

open TypeTower Value

universe w

namespace KnightRealization

variable {M : Type w}

/-- The model class is closed under reduction (`IsModel.reduct`, #101/#112): the reduct-closure
hypothesis of the generic layer, discharged once for Knight. -/
theorem isModelClass_reduct {δ δ' : LimitStage} (h : δ ≤ δ') {N : Type w}
    (R' : KnightRealization δ' N) (hR' : IsModelClass R') : IsModelClass (R'.reduct h) :=
  hR'.reduct h

/-! ### Prolongation through a block -/

/-- A model of `S^ω` (a realization at `blockStage 0`) **prolongs through block `ξ`**: it
prolongs, through actual models, to the failed target `blockStage (ξ + 1)` of block `ξ`
(terminal level `blockStage ξ`).  Intrinsic — defined from `ProlongsToIn IsModel`, not from a
selected history. -/
def ProlongsThroughBlock (R : KnightRealization (blockStage 0) M) (ξ : Ordinal.{0}) : Prop :=
  Realization.ProlongsThroughBlock IsModelClass blockStage blockStage_mono R ξ

/-- Prolongation through block `ξ` of an **isomorphism class of stage-`ω` realizations with
model-certified prolongation targets** (lift of the certified `ProlongsToClassIn IsModel`;
`IsModelClass` constrains the target, not the source — the quotient contains all stage-`ω`
realizations; restricting/transporting to `knightModelSetoid` and the sentence-model quotient
is #77). -/
def ProlongsThroughBlockClass (q : Quotient (Realization.isoSetoid knightTower (blockStage 0) M))
    (ξ : Ordinal.{0}) : Prop :=
  Realization.ProlongsThroughBlockClass IsModelClass blockStage blockStage_mono q ξ

@[simp]
theorem prolongsThroughBlockClass_mk (R : KnightRealization (blockStage 0) M) (ξ : Ordinal.{0}) :
    ProlongsThroughBlockClass (Quotient.mk _ R) ξ ↔ R.ProlongsThroughBlock ξ := Iff.rfl

/-! ### The stopping rank -/

/-- `R` **has a failure**: some block is not prolonged through.  Totality (every model of `S^ω`
has a failure below `ω₁`) is #30/#31's theorem. -/
def HasFailure (R : KnightRealization (blockStage 0) M) : Prop :=
  Realization.HasFailure IsModelClass blockStage blockStage_mono R

/-- The **stopping rank** (stopping index) of a model of `S^ω`: the least block it does not
prolong through, `sInf {ξ | ¬ R.ProlongsThroughBlock ξ}`.  Caveat: `sInf ∅ = 0`, so without
`HasFailure` the value `0` carries no information; under `HasFailure` it is the first failed
block (`stopRank_mem`, `prolongsThroughBlock_iff_lt_stopRank`).  Its terminal level is
`stopLevel R = blockLevel (stopRank R)`; its failed target is `blockLevel (stopRank R + 1)`. -/
noncomputable def stopRank (R : KnightRealization (blockStage 0) M) : Ordinal.{0} :=
  Realization.stopRank IsModelClass blockStage blockStage_mono R

/-! ### Isomorphism invariance and the class rank -/

theorem stopRank_eq_of_iso {N : Type w} {R : KnightRealization (blockStage 0) M}
    {R₂ : KnightRealization (blockStage 0) N} (h : Nonempty (R.Iso R₂)) :
    stopRank R = stopRank R₂ :=
  Realization.stopRank_eq_of_iso h

/-- Termination (`HasFailure`) on isomorphism classes of stage-`ω` realizations with
model-certified prolongation targets. -/
def HasFailureClass (q : Quotient (Realization.isoSetoid knightTower (blockStage 0) M)) : Prop :=
  Realization.HasFailureClass IsModelClass blockStage blockStage_mono q

@[simp]
theorem hasFailureClass_mk (R : KnightRealization (blockStage 0) M) :
    HasFailureClass (Quotient.mk _ R) ↔ HasFailure R := Iff.rfl

/-- The **stopping rank of an isomorphism class of stage-`ω` realizations with model-certified
prolongation targets** — the rank the counting kernel consumes once the `stopRank < ω₁` bound
(totality) and countable fibres are supplied (#30/#31; #77 transports the `< ω₁` theorem, not
merely `HasFailure`). -/
noncomputable def stopRankClass
    (q : Quotient (Realization.isoSetoid knightTower (blockStage 0) M)) : Ordinal.{0} :=
  Realization.stopRankClass IsModelClass blockStage blockStage_mono q

@[simp]
theorem stopRankClass_mk (R : KnightRealization (blockStage 0) M) :
    stopRankClass (Quotient.mk _ R) = stopRank R := rfl

end KnightRealization

end VaughtConjecture.Knight
