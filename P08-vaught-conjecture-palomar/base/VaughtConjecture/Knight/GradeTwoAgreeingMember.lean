/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoInvariant

set_option linter.privateModule false

/-! # The two-level tower: constructing the agreeing retained member

`lift_of_agreeing_member` (`Knight/GradeTwoBountifulTest.lean`) lifts a prescribed input over the
row of a retained member `m` at `m`'s cap once a retained member `m'` extends the input literally
and agrees with `m` on the **full decoded vector** under `m`'s cap.  This module constructs `m'`
for the coded inputs that `Member` actually represents — the prescribed labelling is the row of a
retained member `mp` restricted to `D⟨C,2⟩` — from an explicit base obligation, and isolates the
one clause of full-vector agreement that the counted recoding must supply.

* **The base obligation** `CodedBountiful sem₀ I`: bountifulness of the base at the pair
  `⟨C,2⟩ ≺ ⟨A,2⟩` with alphabet-valued inputs and output, under alphabet caps.  It is derived
  from ordinary bountifulness of the base in `Knight/GradeTwoCodedBountiful.lean`
  (`codedBountiful_of_isBountiful`).
* **The member** `agreeingMember`: the base output, capped at the larger of the two caps; it is
  alphabet-valued, respects the base, is retained whenever the family predicate depends only on
  the cells under `C` (`hPC`), extends `mp` literally under `C`, and agrees with `m` under `m.γ`
  at every base cell (`agreeingMember_agree`).
* **Full-vector agreement** (`levelCap_eq_of_agree`): base agreement together with agreement of
  the **level-one readings** under `m.γ` gives `levelCap m m' = m.γ`, the hypothesis of the lift.
* **The level-one clause** `ReadOneStable m`: a member agreeing with `m` under `m.γ` at every base
  cell, with at least `m`'s cap, has its decoded level-one readings agree with `m`'s under `m.γ`.
  It holds trivially when the grade-`≤ 1` parts coincide (`readOne_agree_of_low_eq`: the witnesses
  are then the same member and the decoder differs only at its cap, `shift_min_of_le`), and in
  general by the stability of the counted recoding under the cap
  (`Knight/GradeTwoReadOneStable.lean`, `readOneStable_of_member`).
* **The lift for coded inputs** (`lift_of_coded_input`): under the base obligation and
  `ReadOneStable m`, the literal clause instance at `⟨C,2⟩ ≺ ⟨A,2⟩` with ambient `memberRow m`,
  cap `m.γ` and prescribed input `memberRow mp ↾ D⟨C,2⟩` has a lift by controller change to
  `agreeingMember`; unconditionally in `Knight/GradeTwoReadOneStable.lean`
  (`lift_of_coded_input'`).

Arbitrary ambient labellings (not member rows) are not addressed.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan CellScheme Transform Value ExtOrd

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

/-! ## The decoder under a larger cap -/

/-! ## The base obligation -/

/-! ## The member -/

section Construct

variable {sem₀ : Semantics D₀} {I : ℕ} {P : (BaseCells D₀ 2 → ExtOrd) → Prop}

variable (C : Finset ι) (hC : (C, 2) ∈ Plan.gradedPlan D₀.plan)
  (hCA : C ≠ A) (m mp : Member sem₀ I 2 P)
  (hagree : ∀ d : BaseCells D₀ 2, D₀.scope d.1 ⊆ C → min (mp.F d) m.γ = min (m.F d) m.γ)
  (hPC : ∀ F F' : BaseCells D₀ 2 → ExtOrd, (∀ d, D₀.scope d.1 ⊆ C → F d = F' d) → P F → P F')

end Construct

/-! ## Full-vector agreement and the level-one clause -/

section Agreement

variable {sem₀ : Semantics D₀} {I : ℕ} {P : (BaseCells D₀ 2 → ExtOrd) → Prop}
  (hI : Fintype.card (Cell D₀) + 2 ≤ I)

end Agreement

/-! ## The lift for coded inputs -/

variable (sem₀ : Semantics D₀) (I M : ℕ) (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M P hAk hI hproper

/-- The tower's lower sets. -/
local notation "Tbelow" => CellScheme.below (tower sem₀ I M P hAk)
/-- The member row of a level-two member. -/
local notation "MROW" => memberRow sem₀ I M P hAk hI hproper

end VaughtConjecture.Knight
