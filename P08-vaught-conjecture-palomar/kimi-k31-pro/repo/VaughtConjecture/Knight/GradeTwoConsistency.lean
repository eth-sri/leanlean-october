/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoTower

set_option linter.privateModule false

/-! # Consistency of the two-level tower: the localities

Every new row of the tower (`Knight/GradeTwoTower.lean`) is local at every lower controller,
derived from the actual rows:

* **at an old controller**: the member's base locality, reindexed along the old lower set
  (`locality_at_old`);
* **at a level-one controller from a level-one row**: the identity shifter with the step
  suppressor at the level cap — base cells agree below the cap (`min_eq_of_levelCap`), siblings
  by the capped ultrametric identity (`min_levelCap_eq`) (`locality_one_one`);
* **at a level-one controller from a level-two row**: `Factorization.locality` with the owned
  witness and the decoder — (13) holds by construction (`factor_old`, `factor_new`), (14) is the
  level-one cap identity between the witness and the controller (`locality_two_one`);
* **at a level-two controller from a level-two row**: the identity shifter with the step
  suppressor at the level cap of the full decoded vectors (`locality_two_two`);
* **from a mute row**: the bottom transformation (`locality_mute`).

The availability clauses and the assembly into `towerSem_consistent` follow in
`Knight/GradeTwoAvailability.lean`.

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
/-- A new cell. -/
local notation "NEW" => addFull.new (hlevel sem₀ I M P hAk)
/-- An old cell. -/
local notation "OLD" => addFull.old (hlevel sem₀ I M P hAk)
/-- The lower-set equivalence of a new cell. -/
local notation "BN" => addFull.belowNew (hlevel sem₀ I M P hAk)
/-- The lower-set equivalence of an old cell. -/
local notation "BO" => addFull.belowOld (hlevel sem₀ I M P hAk) hproper
/-- The level of a new cell. -/
local notation "LV" => level sem₀ I M P
/-- The member of a new cell. -/
local notation "MEM" => memOf sem₀ I M P
/-- The row of a new cell. -/
local notation "ROW" => newRow sem₀ I M P hI

/-! ## Evaluating the rows -/

/-! ## Rows evaluated on identified members -/

/-! ## Locality at an old controller -/

/-! ## Locality at a level-one controller, from a level-one row -/

/-! ## Locality at a level-one controller, from a level-two row -/

/-! ## Locality at a level-two controller, from a level-two row -/

/-! ## Locality from a mute row -/

end VaughtConjecture.Knight
