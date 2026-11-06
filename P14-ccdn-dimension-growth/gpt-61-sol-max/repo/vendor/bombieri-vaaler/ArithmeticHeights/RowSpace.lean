/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Subspace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank

-- Only the worked examples below mention `Matrix.mulHeight`, the height of the entries of
-- Layer 2.5, and they mention it in order to distinguish it from the height of the row space.

/-!
# The row space of a matrix and the height of its maximal minors

The dictionary between a matrix of full row rank and the subspace it spans: the Plücker
coordinates of the row space are the maximal minors, so the height of the row space is the height
of the tuple of minors, and left multiplication by an invertible matrix — a row operation — leaves
it unchanged. That invariance is what distinguishes the height of the row space from
`Matrix.mulHeight`, the height of the entries of Layer 2.5, and it is the reason Bombieri–Vaaler
can improve on the naïve Siegel bound.

## Main definitions

None, deliberately. The row space of `A` is `Submodule.span R (Set.range A.row)`, which is
Mathlib's `LinearMap.range A.vecMulLinear` by `range_vecMulLinear`, and the tuple of maximal minors
is `exteriorPower.plucker m A.row` of Layer 3.1. A third name for either would force every later
statement to choose between three spellings of one object.

## Main results

* `Matrix.plucker_row_eq_det_submatrix`: the Plücker coordinate of `A` at a set `s` of columns is
  the determinant of the submatrix on those columns, taken in increasing order. This is the index
  identification, and `Matrix.plucker_row_eq_det_submatrix_orderIso` restates it with
  `Finset.orderIsoOfFin` in place of `Finset.orderEmbOfFin`.
* `Matrix.plucker_row_mul`: `plucker m (U * A).row = U.det • plucker m A.row`, for *every* square
  `U` and over any commutative ring — Bombieri–Vaaler (2.5), and the quantitative form of the
  invariance.
* `Matrix.span_range_row_mul`: for `U` of unit determinant the row space itself is unchanged, whence
  `Matrix.mulHeight_span_range_row_mul` and its Arakelov and absolute companions.
* `Matrix.mulHeight_span_range_row` and `Matrix.arakelovMulHeight_span_range_row`: the height of the
  row space is the height of the tuple of maximal minors — `H(A)` and `H_Ar^row(A)` of the
  literature, neither of which is `Matrix.mulHeight A`.
* `Matrix.linearIndependent_row_iff_rank_eq` and
  `Matrix.linearIndependent_row_iff_plucker_row_ne_zero`: full row rank, in the two forms that the
  statements above take as a hypothesis.

## Implementation notes

The invariance under row operations is not a theorem about heights. `Matrix.span_range_row_mul` is
an equality of submodules, and every height statement below is one `congrArg` away from it,
because Layer 3.2 defines the height of a subspace as a function of the subspace alone. The
mathematical content sits in that span equality and, quantitatively, in `Matrix.plucker_row_mul`.

`Matrix.plucker_row_mul` needs no hypothesis on `U`, no field, and no expansion of an alternating
map along a matrix — which is fortunate, since Mathlib has no such expansion. The proof is Layer
3.1 used twice: `exteriorPower.plucker_fin_eq_det` says that the single Plücker coordinate of a
square family is its determinant, so the wedge of the rows of `U` is `U.det` times the wedge of the
standard basis; and `exteriorPower.plucker_eq_smul_iff` transports a proportionality of coordinate
tuples to one of wedges. `exteriorPower.map` then pushes the relation along `A.vecMulLinear`,
whose composition with the rows of `U` is the rows of `U * A` — by `rfl`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Remark 2.8.7 for the dictionary, Definition 2.8.11 for the Arakelov normalization of the row-space
height, and 2.9.8 for the height of the entries, which is a different number and is Layer 2.5 here.
E. Bombieri and J. Vaaler, "On Siegel's lemma", *Inventiones Mathematicae* **73** (1983), 11–32,
equation (2.5), where the invariance is the statement that the height is intrinsic on the
Grassmannian. W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations",
*Annals of Mathematics* **85** (1967), 430–472, §1.

This is Layer 3.3 of the `ArithmeticHeights` roadmap.
-/

public section

namespace Matrix

open Module Submodule exteriorPower

/-!
### The Plücker coordinates of a matrix are its maximal minors
-/

section Minors

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- **The Plücker coordinates of a matrix are its maximal minors.** The coordinate at a set `s` of
`m` columns is the determinant of the submatrix on those columns, enumerated in increasing order.
The enumeration is Mathlib's `Finset.orderEmbOfFin`, the one `Set.powersetCard.ofFinEmbEquiv`
already fixes, so no later statement has to choose it again. -/
theorem plucker_row_eq_det_submatrix (A : Matrix (Fin m) ι R) (s : Set.powersetCard ι m) :
    plucker m A.row s =
      (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [plucker_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rfl

end Minors

/-!
### Row operations multiply the Plücker coordinates by a determinant
-/









/-!
### The row space
-/






/-!
### Full row rank
-/

section Rank

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {m : ℕ}

/-- **Full row rank, in minors**: a matrix has independent rows exactly when some maximal minor is
nonzero. This is `exteriorPower.plucker_eq_zero_iff` of Layer 3.1, and it is what makes the height
of the row space a statement about a nonzero tuple. -/
theorem linearIndependent_row_iff_plucker_row_ne_zero [LinearOrder ι] (A : Matrix (Fin m) ι K) :
    LinearIndependent K A.row ↔ plucker m A.row ≠ 0 := by
  rw [ne_eq, plucker_eq_zero_iff, not_not]

end Rank

/-!
### The height of the row space
-/










end Matrix

/-!
### Worked examples
-/

section Examples

open Matrix Submodule exteriorPower

end Examples

end
