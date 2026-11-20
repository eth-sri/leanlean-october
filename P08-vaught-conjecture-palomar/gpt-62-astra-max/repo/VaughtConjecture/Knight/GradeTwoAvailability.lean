/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoConsistency

set_option linter.privateModule false

/-! # The two-level tower: availability, consistency, coding, completeness

* **Availability** of every new row toward every index of its lower set (`availability_new`):
  toward a proper index by the member's base availability; toward `(A, 1)` by a level-one member
  itself (its self-reading is its cap, `levelCap_self`) or by the owned witness of a level-two
  member (whose decoded reading of the witness is the member's cap, `dec_witness_cap`); toward
  `(A, 2)` by the level-two member itself.  Every reading of a member's row is under its cap
  (`row_le_cap_one`, `row_le_cap_two`).
* **Consistency** of every new row (`respects_new`, from the localities of
  `Knight/GradeTwoConsistency.lean`) and of the whole semantics (`towerSem_consistent`, with
  the base rows).
* **Coding** (`towerSem_isCoded`) and **completeness** (`tower_complete`).

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}
  (sem₀ : Semantics D₀) (I M : ℕ) (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M P hAk hI hproper

/-- The tower semantics' rows. -/
local notation "SE" => Semantics.E (towerSem sem₀ I M P hAk hI hproper)
/-- The tower's lower sets. -/
local notation "Tbelow" => CellScheme.below (tower sem₀ I M P hAk)
/-- The tower's graded indices. -/
local notation "Tcell" => CellScheme.cell (tower sem₀ I M P hAk)
/-- The tower's grades. -/
local notation "Tgrade" => CellScheme.grade (tower sem₀ I M P hAk)
/-- The tower's scopes. -/
local notation "Tscope" => CellScheme.scope (tower sem₀ I M P hAk)
/-- A new cell. -/
local notation "NEW" => addFull.new (hlevel sem₀ I M P hAk)
/-- An old cell. -/
local notation "OLD" => addFull.old (hlevel sem₀ I M P hAk)
/-- The lower-set equivalence of a new cell. -/
local notation "BN" => addFull.belowNew (hlevel sem₀ I M P hAk)
/-- The level of a new cell. -/
local notation "LV" => level sem₀ I M P
/-- The member of a new cell. -/
local notation "MEM" => memOf sem₀ I M P
/-- The row of a new cell. -/
local notation "ROW" => newRow sem₀ I M P hI

/-! ## Every reading is under the cap -/

/-! ## The self-readings -/

/-! ## Availability -/

/-! ## Consistency -/

/-! ## Coding -/

/-! ## Completeness -/

end VaughtConjecture.Knight
