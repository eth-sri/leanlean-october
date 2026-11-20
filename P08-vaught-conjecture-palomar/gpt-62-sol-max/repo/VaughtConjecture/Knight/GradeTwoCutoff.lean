/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoAvailability
public import VaughtConjecture.Knight.FullScopeZeroExtension
public import VaughtConjecture.Knight.FiniteCutoffBound
public import VaughtConjecture.Knight.RowReadback

/-! # The two-level tower: the intended section and the cutoff forcing at a controller

**Part one of the acceptance test — the intended section exists.**  Every level-two member `m`
extends to a labelling respecting the whole tower semantics: its own row on the lower set of
its cell, `⊥` above grade two (`section_of_member`, by the full-scope zero extension of
`Knight/FullScopeZeroExtension.lean`).  The section carries the member's base labels literally
(`section_old`) and reads the member's cell at its cap (`section_self`).  A coded display —
context labels and requested labels in the alphabet at grade two, respecting the base, under a
cap — is a member, so its intended section exists.

**Part two — the forcing at a controller.**  At any cell `Sig` of any scheme whose row satisfies
the cutoff bound for reference data on its lower set, a respecting labelling that activates
`Sig` **above the cap** — `s Sig ≠ ⊥` and `s cap ≤ s Sig` — and carries the proper reference
`β + j` at the representative reads the request at least `β`: `truncExt β (s req) = ⊤`
(`readback_at_controller`: locality at `Sig` transports the bound, `CutoffBound.readback_top`
finishes).  On the tower, the display member's cell is such a controller (`tower_readback`).

**What this does not yet give.**  A respecting labelling may activate the display's cell *below*
the cap, `⊥ < s Sig < s cap`, and rely on another level-two member for availability; then the
transported bound is capped at `s Sig` and the request is forced only above `min β (s Sig)`.
Forcing it for every activating labelling requires every member dominating the cap to be
cutoff-correct — the correctness thinning of Def. 8.3.2 on this tower, carried out through the
family predicate in `Knight/GradeTwoForcing.lean` (`tower_readback_of_availability`); the thinned
family's bountifulness (§§9.1, 9.4–9.6) is not proved.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι}

/-! ## The forcing at a controller, for any scheme -/

/-! ## The tower -/

variable {D₀ : CellScheme A} (sem₀ : Semantics D₀) (I M : ℕ) (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
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
/-- The lower-set equivalence of a new cell. -/
local notation "BN" => addFull.belowNew (hlevel sem₀ I M P hAk)
/-- The member of a new cell. -/
local notation "MEM" => memOf sem₀ I M P

omit hI hproper in
/-- The cell of a level-two member. -/
noncomputable def memberCell (m : Member sem₀ I 2 P) : Cell (tower sem₀ I M P hAk) :=
  NEW (idx sem₀ I M P (Sum.inr (Sum.inl m)))

omit hI hproper in
theorem cell_memberCell (m : Member sem₀ I 2 P) : Tcell (memberCell sem₀ I M P hAk m) = (A, 2) := by
  unfold memberCell
  rw [addFull.cell_new, level_idx]
  rfl

/-- **The row of a level-two member on the lower set of `(A, 2)`.** -/
noncomputable def memberRow (m : Member sem₀ I 2 P) : Tbelow (A, 2) → ExtOrd :=
  fun d => SE (memberCell sem₀ I M P hAk m) ⟨d.1, (cell_memberCell sem₀ I M P hAk m).symm ▸ d.2⟩

/-! ## The forcing on the tower -/

end VaughtConjecture.Knight
