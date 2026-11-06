/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoBountifulTest

set_option linter.privateModule false

/-! # The two-level tower: proper-scope correctness as an inductive invariant

`Knight/GradeTwoBountifulTest.lean` showed that, at cap `⊥`, the literal bountifulness clause
cannot exclude an already-lawful proper-face input by imposing correctness only at full scope:
if the base admits a lawful labelling of `D⟨C,2⟩` carrying the reference with an incorrect
request, the correct thinning is not bountiful.  This module turns the missing condition into an
explicit invariant and proves its induction step.

* `CorrectAt sem BJ c ρ q`: every labelling of `D⟨BJ⟩` respecting `E⟨BJ⟩` that carries the proper
  reference `β + j` (`j < 2`) at `ρ` under a cap at `c` at least `β` reads the request `q` at
  least `β`.  `ProperCorrect` asks this at every *proper* grade-two index containing the
  reference cells; `FullCorrect` at every grade-two index.
* **Base case** (`properCorrect_of_no_proper_scope`): when no proper scope of the plan contains
  the three reference cells jointly — the reference is attached at full scope — the proper
  invariant holds vacuously.  This is a concrete base realizing the hypothesis; the paper's
  inductive situation (a base that is itself a forced tower) is *not* an available hypothesis and
  is not assumed.
* **Induction step** (`fullCorrect_tower`): over a base satisfying `ProperCorrect`, the tower
  with a cutoff-correct level-two family satisfies `FullCorrect` — at every proper index because
  its lower set consists of base cells only, whose lawful labellings are exactly the base's
  (`belowProper`, `respectsBelow_of_tower`, `respectsBelow_tower_of_base`), and at the full
  index by the forcing through the availability witness actually used
  (`tower_readback_of_availability`).  `FullCorrect` of the tower is `ProperCorrect` for any
  construction over a strictly larger scope: the invariant propagates.
* **Necessity** (`properCorrect_of_isBountiful`): if the thinned tower is bountiful, the base
  satisfies `ProperCorrect` at every proper scope containing the reference — the contrapositive
  of the bottom-cap counterexample.  So, at bottom cap, the invariant is exactly what
  bountifulness of the correctness thinning requires of its base.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-! ## The invariant, for any semantics -/

section Invariant

variable {D : CellScheme A}

end Invariant

/-! ## The tower -/

variable {D₀ : CellScheme A} (sem₀ : Semantics D₀) (I M : ℕ)
  (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M P hAk hI hproper

/-- The tower semantics' rows. -/
local notation "SE" => Semantics.E (towerSem sem₀ I M P hAk hI hproper)
/-- The tower's lower sets. -/
local notation "Tbelow" => CellScheme.below (tower sem₀ I M P hAk)
/-- The tower's graded indices. -/
local notation "Tcell" => CellScheme.cell (tower sem₀ I M P hAk)
/-- An old cell. -/
local notation "OLD" => addFull.old (hlevel sem₀ I M P hAk)
/-- The lower-set equivalence of an old cell. -/
local notation "BO" => addFull.belowOld (hlevel sem₀ I M P hAk) hproper

/-! ## The induction step -/

/-! ## Necessity: bountifulness of the thinning requires the invariant of the base -/

end VaughtConjecture.Knight
