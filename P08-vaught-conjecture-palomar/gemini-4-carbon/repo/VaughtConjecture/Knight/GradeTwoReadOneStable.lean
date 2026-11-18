/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.GradeTwoAgreeingMember

set_option linter.privateModule false

/-! # The level-one clause: decoded readings are stable under capped agreement

`ReadOneStable m` (`Knight/GradeTwoAgreeingMember.lean`) asks that every member `m'` agreeing
with `m` under `m`'s cap `γ = ofOrd g` at every base cell, with at least that cap, has its decoded
level-one readings agree with `m`'s under `γ`.  This module proves it for every member
(`readOneStable_of_member`), through the counted recoding:

* **Keys under the cap are stable** (`mem_keys_iff_of_lt`): the value sets `S` of `m.low` and
  `S'` of `m'.low` have the same keys below `g` — a value of `S` is at most `g`, and a value at
  least `g` has key at least `g` (`le_keyOrd_of_le`, since `g` is self-visible at grade two).
  Hence blocks and codes of values below `g` coincide (`blockOfKey_eq_of_lt`, `code_eq_of_lt`),
  and every key at least `g` has block beyond the low keys (`le_blockOfKey_of_ge`).
* **The witness vectors agree under the code cap** `c₀ = ω·(n+1) + 1`, `n` the number of low
  keys (`witness_agree`): at a cell where `m.low` is below `g` the codes are equal; where it is
  `g` the code is `c₀` and `m'`'s code is at least `c₀` (its value is at least `g`, its finite
  part at least one by orderliness).
* **The level caps with any level-one member agree under `c₀`** (`levelCap_min_eq`): the
  capped ultrametric identity for agreement caps and rounding commuting with capping.
* **The decoders agree under `γ`** (`shift_min_eq_of_agree`): an input below `c₀` is common to
  both and decodes through the same hosted key (`keyAt_eq_of_le_lowCount`); an input at least
  `c₀` decodes on both sides to at least `γ` (`ofOrd_le_shift_of_lowCount_lt`).

With it, `lift_of_coded_input` holds unconditionally for coded inputs
(`lift_of_coded_input'`): the agreeing retained member agrees with the ambient controller on the
full decoded vector, level-one readings included.

Construction-private (not root-exported). -/

@[expose] public section

namespace VaughtConjecture.Knight

open AmalgamationPlan Value ExtOrd

/-! ## Keys under a cap -/

section Keys

variable (g : Ordinal.{0})

variable {g}

variable {S S' : Finset Ordinal.{0}}

end Keys

/-! ## Level caps under the code cap -/

/-! ## The members -/

variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D₀ : CellScheme A}

section Members

variable {sem₀ : Semantics D₀} {I : ℕ} {P : (BaseCells D₀ 2 → ExtOrd) → Prop}
  (hI : Fintype.card (Cell D₀) + 2 ≤ I)

section Stable

variable (m m' : Member sem₀ I 2 P) {g : Ordinal.{0}} (hg : m.γ = ofOrd g)
  (hbase : ∀ d, min (m'.F d) m.γ = min (m.F d) m.γ)

include hg hbase

end Stable

end Members

/-! ## The lift for coded inputs, unconditionally -/

variable (sem₀ : Semantics D₀) (I M : ℕ) (P : (BaseCells D₀ 2 → ExtOrd) → Prop)
  (hAk : ∀ k, 1 ≤ k → k ≤ M + 2 → (A, k) ∈ Plan.gradedPlan D₀.plan)
  (hI : Fintype.card (Cell D₀) + 2 ≤ I) (hproper : ∀ i : Cell D₀, D₀.scope i ≠ A)

include sem₀ I M P hAk hI hproper

/-- The tower's lower sets. -/
local notation "Tbelow" => CellScheme.below (tower sem₀ I M P hAk)
/-- The member row of a level-two member. -/
local notation "MROW" => memberRow sem₀ I M P hAk hI hproper

end VaughtConjecture.Knight
