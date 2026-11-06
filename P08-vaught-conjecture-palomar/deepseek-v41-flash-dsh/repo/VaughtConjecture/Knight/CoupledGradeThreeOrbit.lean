/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.CoupledGradeThreeConstraints

/-! # Grade three: the moving source orbit, and the audit of the source orbits

**The generic law** (`orbit_bounds_probe`, after the research scout `orbit_bounds_controller`):
in a row transformed onto the probes `min (value e) (value c)` of a controller `c`, if the
source at `e` is the replacement `(grade c, grade c)` of the source at `d` (`grade d ≤ grade c`),
then `min (value e) (value c) ≤ R (value d)` with `R` that replacement.  When `value d < value c`
the row equation at `d` is uncapped, `σ (source d) = value d ≤ g (grade c)` (`shifter_eq_of_lt`),
so clause 5 is active at the controller's grade; otherwise inflationarity of replacement gives
the bound outright.  The same activation fixes the label at `d` under every index-`i` replacement
that fixes its source (`orbit_fixes_label`).

**The actual orbit** (`A₁c_le_R₃_of_respects`, the research scout's `actual_A₁c_bound`): the
proper source `ω+1` is replaced by `a₁`'s controller's diagonal `ω+3` at threshold three
(`v₀_orbit_three`), so `z₁ = q A₁c ≤ R₃ v` for every proper grade-one label `v` — a constraint
coupling `z₁` to the proper label that order and visibility do not give (`v = 2`, all upper labels
`ω+3` passes every constraint of `CoupledGradeThreeConstraints` and fails this one, `R₃ 2 = 3`).
The same orbit in `b₁`'s controller's row bounds the same label (`A₁c_le_R₃_of_respects'`), and
in `a₂`'s controller's row likewise.  **The sharp form** (`A₁c_eq_R₃_of_lt`, through the index-one
replacement `v₀_orbit_three_one` and the ordinal law `eq_R₃_of_orbit`): if `v < z₁` then
`z₁ = R₃ v` exactly, and `v` has finite part one.  So either `z₁ ≤ v`, or `v = ω·b+1` and
`z₁ = ω·b+3`.

**The audit of the source orbits** (the clause-5 pairs `(α, k, i)`, `α` a row value, `k` the
controller's grade, `i ≤ k`, with the row values of the frozen rows).  Grade-three rows read
`⊥`, `ω+1`, `ω+3`, `ω+4`, `ω·2+3`; at threshold three, `ω+3`, `ω+4`, `ω·2+3` and `⊥` are fixed,
`ω+1 ↦ ω+3` at index three is the orbit above, `ω+1 ↦ ω+1` at index one is the fixing law, and
`ω+1 ↦ ω, ω+2` at indices zero and two land on non-sources (they constrain the shifter off the
row only).  At thresholds one and two every row value is fixed or lands on a non-source
(`ω+1 ↦ ω+2`).  At threshold four (above the controller's grade) the clause is active only where
`σ α ≤ g 4`, and `g 4` is bounded below by no label of `(univ, 3)`; what it forces
unconditionally is the bottom coupling `A₂c_eq_bot_of_A₁c` (`ω+3 ↦ ω+4`).  The copy `b₁new`'s
row reads only `⊥`, `ω+1`, `ω·2+3`: no orbit lands on a source.  At grades one and two the only
moving orbits landing on sources are `ω·2+1 ↦ ω·2+2` (threshold two, above the grade-one
controller) and `ω·2+2 ↦ ω·2+3` (threshold three, above the grade-two controller), whose
unconditional content is the bottom couplings already extracted (`U_H_eq_bot_of_H₀old`,
`U_S_eq_bot_of_s₀old`); `ω+1 ↦ ω+2` at threshold two lands on a non-source.  So the moving
orbit `ω+1 ↦ ω+3` is the one source orbit at the controllers' own grades, and it is compiled
here.

Necessary constraints only; the augmented list is not claimed sufficient.  Not done: the
grade-three retuning.  Construction-private. -/
@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)


/-! ## Generic: a moving source orbit bounds the probes -/

section Generic

variable {D : Type*} (grade : D → ℕ) (source value : D → ExtOrd) {c d : D}
  (hd : grade d ≤ grade c)
  (h : TransformsTo grade source (fun e => min (value e) (value c)))

end Generic

/-! ## The sharp ordinal consequence -/

section Sharp

end Sharp

/-! ## The actual orbit at grade three -/

section Actual


end Actual

end VaughtConjecture.Knight
