/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import VaughtConjecture.Knight.TwoContextPrescribedPair

/-!
# Separating the forced witness-copy identification: necessary conditions, and the local test

The fixed glue `rows₂` identifies the two occurrences of input A's level-one witness (`H₀old`
on the A face, `H₀new` on the fresh B face): every non-mute controller reads the same source at
both, so rigidity forces equal labels.  This scout records what **any** semantics on `D₂` must do
for the specified pair (`ω+4` at `H₀old`, `ω·2+3` at `H₀new`) to be realized by a respecting
labelling — with both input faces (cells, rows, labels) untouched:

* `exists_separating_controller`: at every grade `j ∈ {1,2,3}` at which the B face carries a
  label `≥ ω·2+3`, some full-scope controller `U` of grade `j` is labelled `≥ ω·2+3` and reads a
  **strictly smaller** source at `H₀old` than at `H₀new` (its row separates the occurrences);
* `le_γ₀_of_row_eq`: every controller reading equal sources at the two occurrences is labelled
  `≤ ω+4` (so the unmodified pulled-back controllers can never dominate the B-face labels);
* `IsConsistent.le_of_probe_eq`: at a separating consistent controller `c`, every intermediate
  cell `Sig` reading equal sources is read by `c` at most its `H₀old` value (the cross entries
  are bounded by the old value);
* `IsConsistent.exists_dominating`: at a consistent controller `c`, a value at a cell of the
  **same grade as `c`** is dominated by an entry of `c` at a cell of `c`'s own graded index.  For
  `H₀new` this is row availability at grade one only: at the grade-one controller the diagonal
  (the only full-scope grade-one cell) must be raised as well.  At the grade-two and grade-three
  controllers it says nothing about `H₀new`; there availability supplies domination of the
  separating value at a full-scope grade-one cell of the controller's lower set.

**The general no-go** (`not_realizable_of_grade_one_pullback`): the specified pair `(p₀, p₁)` is
realized by no respecting labelling of *any* semantics on `D₂` whose grade-one full-scope
controller reads equal sources at the two occurrences (the fixed glue `rows₂` is the special case,
`not_realizable_rows₂`).

**The local test, passed** (`separating_row_test`): at the grade-one full controller `U_H` (the
fresh full copy of the level-one witness) the request-dependent row `row₃` — the pulled-back row
with the separating value `ω·(k+1)+2` (the successor of the cap code `ω·(k+1)+1`, `k` the number of
keys of the level-one code) at the copy and at the diagonal — is orderly, coded at grade one,
dominated by its diagonal, strictly separates the two occurrences, and its locality clause at the
copy is witnessed by `Witness.raise` on the identity with cutoff `ω·k+2` (strictly between every
proper-cell code and the cap code, finite part `2 > 1`).  Both input faces are untouched.

Not done here: the full modified semantics (the same separation is forced at grades two and three
by input B's labels `ω·2+3` at `s₀` and `b₁`; the raised grade-one value must propagate coherently
through the higher rows' values at the grade-one full controller — a `Witness.lower` flattening
is a proposed proof route, not established), its bountifulness (for `rows₂` proved from the two face obligations
`rows₂_isBountiful_of`, which are stated against the glue's rows and would have to be re-proved
for modified rows), and the respecting labelling itself.  Construction-private. -/

@[expose] public section

set_option autoImplicit false

namespace VaughtConjecture.Knight

open AmalgamationPlan Transform Value ExtOrd
open CellScheme.restrictFace (toCell belowMap pushGraded)

attribute [local instance] decEqRow1 decEqCore2 decEqCappedCore3

/-! ## Generic probe lemmas: strict and equal sources -/

section Probes
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}
  {BJ : Finset ι × ℕ} {q : D.below BJ → ExtOrd}

end Probes

/-! ## Consequences of consistency for a separating controller -/

section Consistent
variable {ι : Type*} [DecidableEq ι] {A : Finset ι} {D : CellScheme A} {sem : Semantics D}

end Consistent

/-! ## The two occurrences in the glued domain -/

section Separating

/-! ### The specified pair: input B's labels on the fresh face force separation at every grade -/

end Separating

/-! ## The separating row at the grade-one full controller: the local test -/

section Construction

/-! ### The values: the cap code `ω·(k+1)+1`, the separating value `ω·(k+1)+2`, the cutoff -/

/-! ### Distinctness of the three cells -/

/-! ### The cells below the copy -/

/-! ### The separating row -/

/-! ### The locality at the copy, witnessed by `Witness.raise` -/

end Construction

end VaughtConjecture.Knight
