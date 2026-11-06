/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoForcing

set_option linter.privateModule false

/-! # The two-level tower: the literal bountifulness clause, tested

The literal clause (Knight, Def. 2.5.14, `Semantics.IsBountiful`) at the proper-to-full pair
`⟨C,2⟩ ≺ ⟨A,2⟩`: a *prescribed* labelling `p` of `D⟨C,2⟩` respecting `E⟨C,2⟩`, an *ambient*
labelling `q` of `D⟨A,2⟩` respecting `E⟨A,2⟩`, a cap `γ` self-visible at grade two, and capped
agreement `(q ∧ γ) ↾ D⟨C,2⟩ = p ∧ γ`; required: `q'` on `D⟨A,2⟩` respecting `E⟨A,2⟩` with
`q' ∧ γ = q ∧ γ` and `q' ↾ D⟨C,2⟩ = p`.  On the tower, `D⟨C,2⟩` consists of base cells only
(`properCell`; the new cells have scope `A ≠ C`), and `D⟨A,2⟩` of the base cells of grade `≤ 2`,
the level-one cells and the level-two cells.  Nothing here demands that any particular controller
be activated: the controller is free to change.

**A genuine counterexample, at cap `⊥`** (`not_bountiful_of_incorrect_proper`).  On a tower whose
level-two family is cutoff-correct for the reference cells `(c, ρ, q)` lying under `C`, suppose
the base admits a lawful labelling `p` of `D⟨C,2⟩` carrying the reference — `p ρ = β + j`,
`β ≤ p c`, `p ρ ≤ p c` — with an *incorrect* request, `truncExt β (p q) ≠ ⊤`.  Then the clause
fails at `(⟨C,2⟩, ⟨A,2⟩, γ = ⊥)`: capped agreement is vacuous, so any lift `q'` extends `p`
literally; `q'` extended by `⊥` above grade two respects the tower; and the forcing through the
availability witness actually used (`tower_readback_of_availability`) reads the request at least
`β` — contradicting `p`.  The required activation is *derived* from the clause's premises
(availability of `q'` at the cap toward `⟨A,2⟩`), not assumed.  Consequently the correctness
thinning is bountiful only over a base that already forces correctness at every proper scope
containing the reference — the situation of the paper's inductive construction, where the base at
`⟨C,2⟩` is itself a forced tower over `C`.

**The lift at cap `⊥`** (`lift_of_member_extends`): whenever `p` extends to a *retained* member
`m` — `m.F = p` on the base cells under `C` — the member's row `memberRow m` is a lift (respect by
consistency; literal restriction by `memberRow_old`).  With the correct thinning this is exactly
the obligation that the counterexample shows can fail: the extension must be correct.

**The lift by controller change at a member's cap** (`lift_of_agreeing_member`).  Take the ambient
to be the row of a retained member `m` and the cap its own cap `m.γ` (self-visible, in the
alphabet).  If some retained member `m'` extends `p` literally and **agrees with `m` under `m`'s
cap** — `levelCap m m' = m.γ`, equivalently `m.γ ≤ agreeCap (fullVec m) (fullVec m')` and
`m.γ ≤ m'.γ` (`levelCap_eq_left_of`) — then `memberRow m'` is a lift: capped agreement holds at
every base cell and every level-one cell by the full-vector agreement
(`memberRow_agree_of_levelCap`), and at every level-two sibling by the capped ultrametric
identity `min_levelCap_eq` — the controller changes from `m` to `m'`, and every sibling's
capped reading is preserved.  The controller freedom that repaired the forcing is what makes this
lift possible: activating the designated `m` instead is exactly what the designated-display
obstruction of `Knight/GradeTwoForcing.lean` rules out.

**What remains open.**  (1) The existence of the retained member `m'` — an alphabet-valued,
correct extension of `p` to all base cells of grade `≤ 2` agreeing with the ambient's controller
under its cap — is a base-level extension obligation, not supplied here.  (2) Ambient labellings
that are not member rows: their controllers activated above the cap must be replaced by
controllers compatible with `p`, subject to the ambient's readings of the replacement cells under
the cap.  (3) Bountifulness at the other graded pairs.  None of these is claimed.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

/-! ## The tower -/

variable (sem₀ : Semantics D₀) (I M : ℕ) (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M P hAk hI hproper

/-- The tower semantics' rows. -/
local notation "SE" => Semantics.E (towerSem sem₀ I M P hAk hI hproper)
/-- The tower's lower sets. -/
local notation "Tbelow" => CellScheme.below (tower sem₀ I M P hAk)
/-- The tower's graded indices. -/
local notation "Tcell" => CellScheme.cell (tower sem₀ I M P hAk)
/-- A new cell. -/
local notation "NEW" => addFull.new (hlevel sem₀ I M P hAk)
/-- An old cell. -/
local notation "OLD" => addFull.old (hlevel sem₀ I M P hAk)
/-- The member of a new cell. -/
local notation "MEM" => memOf sem₀ I M P
/-- The member row of a level-two member. -/
local notation "MROW" => memberRow sem₀ I M P hAk hI hproper

/-! ## A genuine counterexample at cap `⊥` -/

/-! ## The lift at cap `⊥`, and the lift by controller change at a member's cap -/

end VaughtConjecture.Knight
