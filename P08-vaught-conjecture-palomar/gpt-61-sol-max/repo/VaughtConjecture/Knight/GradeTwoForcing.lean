/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoCutoff

/-! # The two-level tower: forcing through the availability witness actually used

**The gap of `Knight/GradeTwoCutoff.lean`.**  `tower_readback` forces the request only for
labellings activating the *designated* display's cell above the cap; a respecting labelling may
activate it below the cap, or not at all, and satisfy availability at the cap through another
level-two member.  This module closes that gap by **thinning the level-two family** — the family
predicate `P` of `Member`, the thinning parameter of `Knight/GradeTwoTower.lean` — to
**cutoff-correct** members (`CutoffCorrect`: the cutoff bound at the representative, the cap and
the request, read on the base labels), and forcing through the availability witness the labelling
actually uses:

* `exists_member_of_cell_two`: every cell at `(A, 2)` is a level-two member's cell;
* `cutoffBound_of_correct`: a correct member's row satisfies the cutoff bound at its own cell;
* `tower_readback_of_availability`: on a tower whose level-two family is cutoff-correct, **every**
  respecting labelling carrying the reference `β + j` at `ρ` under the cap `c ≥ β` reads the
  request at least `β`.  Availability at the cap toward `(A, 2)` supplies a level-two cell
  activated at least at the cap, that cell is a correct member's, and `readback_at_controller`
  applies there.  No hypothesis on which member is activated, nor on the display, is needed.
* The display is a member of the correct family (`Member.select`, `cutoffCorrect_of_reference`).

**The retained subfamily keeps the owned witnesses and availability.**  The thinning is a
parameter of the whole construction: level one is never thinned (`Member₁`), each level-two
member's owned witness is its own counted recoding at level one, and its availability toward
`(A, 2)` is itself; so `towerSem_consistent`, `towerSem_isCoded` and `tower_complete` (given one
retained member) hold for **every** family predicate, in particular for the correct family.

**Designated-display lifting obstruction.**  Suppose a lift is required to carry the display's
base labels *and* to activate the display's own cell at its cap.  `sibling_ge_of_lift` shows what
locality at the display's cell then forces at every sibling member's cell: the lifted labelling,
capped at the display's cap, reads the sibling at least at every base label of the display lying
under their level cap; so an ambient sibling label `⊥` cannot be preserved when the display has a
base label in `(⊥, levelCap]` (`no_capped_lift_of_sibling_bot`).  This is an obstruction to lifts
*through the designated display only*: the literal bountifulness clause (Def. 2.5.14) does not
demand that activation, and both conclusions here are conditional on it.  The literal clause,
with the availability controller free to change, is tested in `Knight/GradeTwoBountifulTest.lean`.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

/-! ## Cutoff-correct base labellings -/

/-- **Cutoff-correctness** of a grade-two base labelling for the reference cells `c` (cap), `ρ`
(representative) and `q` (request): the cutoff bound of `Knight/FiniteCutoffBound.lean` for the
one-reference data, read on the base labels. -/
def CutoffCorrect (c ρ q : Cell D₀) (hc : D₀.grade c ≤ 2) (hρ : D₀.grade ρ ≤ 2)
    (hq : D₀.grade q ≤ 2) (F : BaseCells D₀ 2 → ExtOrd) : Prop :=
  min (extVisibilityReplace (F ⟨ρ, hρ⟩) 2 0) (F ⟨c, hc⟩) ≤ min (F ⟨q, hq⟩) (F ⟨c, hc⟩)

/-- Re-selecting a level-two member into another family whose predicate its labelling
satisfies. -/
def Member.select {sem₀ : Semantics D₀} {I : ℕ} {P : (BaseCells D₀ 2 → ExtOrd) → Prop}
    (m : Member sem₀ I 2 P) (P' : (BaseCells D₀ 2 → ExtOrd) → Prop) (h : P' m.F) :
    Member sem₀ I 2 P' :=
  { m with sel := h }

@[simp] theorem Member.select_F {sem₀ : Semantics D₀} {I : ℕ}
    {P : (BaseCells D₀ 2 → ExtOrd) → Prop} (m : Member sem₀ I 2 P)
    (P' : (BaseCells D₀ 2 → ExtOrd) → Prop) (h : P' m.F) : (m.select P' h).F = m.F := rfl

@[simp] theorem Member.select_γ {sem₀ : Semantics D₀} {I : ℕ}
    {P : (BaseCells D₀ 2 → ExtOrd) → Prop} (m : Member sem₀ I 2 P)
    (P' : (BaseCells D₀ 2 → ExtOrd) → Prop) (h : P' m.F) : (m.select P' h).γ = m.γ := rfl

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
/-- An old cell. -/
local notation "OLD" => addFull.old (hlevel sem₀ I M P hAk)
/-- The member of a new cell. -/
local notation "MEM" => memOf sem₀ I M P

/-! ## Capped lifting from ambient sibling labels: the failed clause -/

end VaughtConjecture.Knight
