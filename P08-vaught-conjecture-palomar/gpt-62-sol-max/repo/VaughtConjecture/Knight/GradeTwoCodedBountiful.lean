/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoReadOneStable
public import VaughtConjecture.Knight.PositiveNormalization

set_option linter.privateModule false

/-! # The coded base obligation from ordinary base bountifulness

`CodedBountiful sem₀ I` (`Knight/GradeTwoAgreeingMember.lean`) asked the base for an
alphabet-valued lift under `max γ δ`.  This module derives it from **ordinary** bountifulness
of the base (`codedBountiful_of_isBountiful`), so that the coded member-extension argument rests
on `sem₀.IsBountiful` alone, with the tower's existing size hypotheses.

* **The alphabet retraction** `alphRetract I`: the identity on `alph 2 I`, sending every other
  label into the alphabet — a value in a block below `I` keeps its block and has its finite part
  cut at `3`; a value at or beyond block `I`, and `⊤`, go to the alphabet's top.  It is a
  bottom-reflecting `2`-step shifter (`isStepShifter_alphRetract`), so it preserves respect
  with the semantic rows unchanged (`RespectsSemanticsBelow.map_bottom_reflecting`), fixes the
  boundary (`alphRetract_eq_self_of_mem_alph`), and commutes with capping (monotone).  Index
  check: for positive `I`, `alph 2 I` is the coded alphabet at block bound `I - 1` and grade `2`.
* **Grade-sensitive capping** (`RespectsSemanticsBelow.gradeCap`): capping a respecting
  labelling at a grade-dependent, antitone family of caps self-visible at their grades preserves
  respect — at each controller the row is capped by the controller's own cap (the Cap Lemma
  `TransformsTo.cap`), the cells below carrying larger caps.  The caps used are the largest
  alphabet values self-visible at each grade below `max γ δ` (`roundDownVis`): a grade-one
  value invisible at grade two survives under the grade-one cap, so no visibility of `δ` is
  needed and the bound `F' ≤ max γ δ` holds as stated.
* **The base bridge** (`baseEquiv`, `RespectsBase.toBelow`, `RespectsBase.ofBelow`): respect of
  the base semantics on the base cells of grade `≤ 2` is respect of `E⟨A,2⟩`.
* **The derivation** (`codedBountiful_of_isBountiful`): the ordinary lift, retracted into the
  alphabet, then capped grade-sensitively.  Literal labels and cap agreement survive both steps
  because the prescribed labels, the ambient labels and the cap are alphabet values below the
  caps.
* **Specialization to the cutoff-correct family** (`cutoffCorrect_congr_of_scope`,
  `lift_of_coded_input_cutoff`): when the prescribed scope contains the three reference cells,
  the family predicate depends only on the cells under it, so the lift by controller change for
  coded inputs holds over any bountiful base — ordinary base bountifulness is the substantive
  inductive hypothesis.  Faces missing a reference cell and arbitrary ambient labellings are not
  addressed, and tower bountifulness is not claimed.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd

/-! ## The alphabet retraction -/

section Retract

variable (I : ℕ)

variable {I}

end Retract

/-! ## Grade-sensitive rounding and capping -/

section GradeCap

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A}

end GradeCap

/-! ## The base bridge -/

section Bridge

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A} {sem₀ : Semantics D₀}

end Bridge

/-! ## The derivation -/

section Derivation

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A} {sem₀ : Semantics D₀}
  {I : ℕ}

end Derivation

/-! ## Specialization to the cutoff-correct family -/

section Cutoff

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

variable (sem₀ : Semantics D₀) (I M : ℕ) (c ρ q : Cell D₀) (hc : D₀.grade c = 2)
  (hρ : D₀.grade ρ ≤ 2) (hq : D₀.grade q ≤ 2)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M c ρ q hc hρ hq hAk hI hproper

/-- The tower's lower sets, over the cutoff-correct family. -/
local notation "Tbelow" =>
  CellScheme.below (tower sem₀ I M (CutoffCorrect c ρ q hc.le hρ hq) hAk)
/-- The member row of a cutoff-correct member. -/
local notation "MROW" =>
  memberRow sem₀ I M (CutoffCorrect c ρ q hc.le hρ hq) hAk hI hproper

end Cutoff

end VaughtConjecture.Knight
