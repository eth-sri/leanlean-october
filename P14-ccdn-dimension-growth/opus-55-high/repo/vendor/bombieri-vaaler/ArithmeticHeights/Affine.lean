/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/

import Mathlib.NumberTheory.Height.NumberField

/-!
# The affine height of a tuple

Mathlib's `Height.mulHeight` is a height on *projective* space: it is invariant under scaling, and
so is a function of the line through a tuple rather than of the tuple. That is the right object
for a point of `ℙⁿ` and the wrong one for anything not homogeneous — the value `∑ i, a i * x i` of
a linear form, or the determinant of a matrix, both of which scale with the tuple. This file adds
the **affine** height, the projective height of the tuple with a coordinate `1` appended:

`Height.mulHeightAff x := Height.mulHeight fun o : Option ι ↦ o.elim 1 x`.

It is the tuple analogue of Mathlib's `Height.mulHeight₁ x = mulHeight ![x, 1]`, and agrees with it
on a one-element tuple (`Height.mulHeightAff_fin_one`). Being a normalization and not a theorem, it
is stated here in Layer 0 rather than at its first use.

`mulHeightAff` is deliberately **not** scaling-invariant, and `Height.exists_mulHeightAff_smul_ne`
records that as a theorem: over `ℚ` the tuples `![1]` and `![2]` have affine heights `1` and `2`.
That failure is the content of the definition, not a defect of it. What survives is one-sided:
the affine height dominates the projective height and the height of every single coordinate, and
is monotone under re-indexing.

## Main definitions

* `Height.mulHeightAff x` for `x : ι → K`, and `Height.logHeightAff x` its logarithm.

## Main results

* `Height.mulHeight_le_mulHeightAff` and `Height.mulHeight₁_le_mulHeightAff`: the affine height
  dominates the projective height of the tuple and the height of each coordinate. The second is
  false for `Height.mulHeight`.
* `Height.mulHeightAff_comp_le` and `Height.mulHeightAff_comp_equiv`: monotonicity under
  re-indexing, and invariance under a bijective one.
* `Height.mulHeightAff_fin_one`: on a one-element tuple the affine height is `Height.mulHeight₁`.
* `Height.exists_mulHeightAff_smul_ne`: the affine height is not scaling-invariant.

## Implementation notes

The appended coordinate is indexed by `none : Option ι` rather than by `Sum.inl` of a `Unit` or by
`Fin.succ`: `Option ι` needs no `Fintype` bookkeeping, inherits `Finite ι` by instance resolution,
and makes re-indexing along `f : ι → ι'` literally `Option.map f`.

No Arakelov analogue is defined here. Layer 0.1 already has the one-variable
`NumberField.arakelovMulHeight₁`, and no bound in the roadmap needs an affine Arakelov height of a
tuple; the Arakelov bounds that would want one carry the constant `1` and need no affine height at
all.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
§1.5, where the affine and projective heights of a point are distinguished throughout.

This is Layer 0.5 of the `ArithmeticHeights` roadmap.
-/

