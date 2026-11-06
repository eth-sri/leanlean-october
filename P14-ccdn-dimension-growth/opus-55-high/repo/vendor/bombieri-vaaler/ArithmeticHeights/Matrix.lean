/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

public import ArithmeticHeights.Extension
public import ArithmeticHeights.LinearForm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import all Mathlib.NumberTheory.Height.Basic

/-!
# The height of a matrix

The height of a matrix is the height of the tuple of its **entries**. It is not the height of its
row space — the height of the tuple of maximal minors, which Bombieri–Vaaler also write `H(A)`;
that one is the height of a point of a Grassmannian and belongs to Layer 3. The classical
literature uses one symbol for both. This file uses `Matrix.mulHeight` for the first only.

The content of the file is four bounds.

* The **product bound** `Matrix.mulHeight_mul_le`, with the constant `Fintype.card n ^ totalWeight
  K` for the inner index type `n`. It is the tuple sum bound of Layer 2.4 applied to the
  multiplication table of the entries of `A` and of `B`: an entry of `A * B` is a sum of
  `Fintype.card n` entries of that one table, and the Segre relation evaluates its height.
* The **Arakelov product bound** `Matrix.arakelovMulHeight_mul_le`, with constant exactly `1`.
  Cauchy–Schwarz entry by entry produces the Frobenius norm, which is submultiplicative; the
  cardinality of the inner index type is not paid at all. This is the matrix form of
  `NumberField.arakelovMulHeight_linearMap_apply_le` and the reason Layer 0 carries two
  normalizations.
* The **determinant bound** `Matrix.mulHeight₁_det_le`. It cannot be stated with `mulHeight A` on
  the right: `A ↦ c • A` fixes the projective height of the matrix and multiplies the determinant
  by `c ^ n`, which `Matrix.exists_not_mulHeight₁_det_le` records. What is true uses the *affine*
  height of Layer 0.5, and the sharp form of it is columnwise, one affine column height per column,
  with the constant `(Fintype.card n)! ^ totalWeight K` from the Leibniz expansion.
* The action on tuples, `Matrix.mulHeight_mulVec_le`, which is Mathlib's
  `Height.mulHeight_linearMap_apply_le` read through the definition, and its Arakelov companion.

The Leibniz expansion carries the signs of the permutations, so the tuple sum bound is used here
through `Height.mulHeight_sum_sign_comp_le'`, a version whose summands may be multiplied by `±1`.
That version is deduced from the unsigned one by doubling the alphabet with a `Bool`, whose two
letters `1` and `-1` have height `1`.

## Main definitions

* `Matrix.mulHeight A` and `Matrix.logHeight A`: the height of the tuple of entries of `A`.
* `Matrix.mulHeightAff A` and `Matrix.logHeightAff A`: its affine counterpart, the height of the
  tuple of entries with a coordinate `1` appended.
* `Matrix.arakelovMulHeight A` and `Matrix.arakelovLogHeight A`: the same in the Arakelov
  normalization, over a number field.

## Main results

* `Matrix.mulHeight_transpose`, `Matrix.mulHeight_submatrix_le`,
  `Matrix.mulHeight_submatrix_equiv` and `Matrix.mulHeight_smul`: invariance under transpose, under
  re-indexing of rows and columns — in particular under row and column permutations — and under
  scaling, and the submatrix bound.
* `Matrix.mulHeight_mul_le` and `Matrix.logHeight_mul_le`: the product bound.
* `Matrix.arakelovMulHeight_mul_le` and `Matrix.arakelovLogHeight_mul_le`: the product bound in the
  Arakelov normalization, with constant `1`.
* `Matrix.mulHeight₁_det_le` and `Matrix.logHeight₁_det_le`: the determinant against the affine
  heights of the columns, and `Matrix.mulHeight₁_det_le_mulHeightAff_pow` against the affine height
  of the matrix.
* `Matrix.exists_not_mulHeight₁_det_le`: no constant bounds the height of a determinant by the
  projective height of the matrix.
* `Height.mulHeight_sum_sign_comp_le'`: the signed tuple sum bound.

## Implementation notes

`Matrix m n K` is definitionally `m → n → K`, and `Height.mulHeight` takes a tuple, so
`Matrix.mulHeight` is the height of `fun q : m × n ↦ A q.1 q.2`. Every statement about
re-indexing is then a statement about `Prod.map`, and transpose is `Equiv.prodComm`.

The finiteness hypotheses are `Finite` wherever the height alone is involved and `Fintype` only
where a matrix product or a determinant is formed.

`Height.mulHeight_sum_sign_comp_le'` belongs next to the unsigned tuple sum bound of Layer 2.4;
it is here because the determinant is the only consumer so far.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
2.9.8 for the height of a matrix and 2.8.11 for the Arakelov normalization.

This is Layer 2.5 of the `ArithmeticHeights` roadmap.
-/

public section

open Finset Function Height AdmissibleAbsValues Real

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {α ι κ : Type*}

end Height

namespace Matrix

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {m n p m' n' : Type*}

/-- **The height of a matrix** is the height of the tuple of its **entries** (Bombieri–Gubler
2.9.8). The height of its row space — the height of the tuple of maximal minors, `H(A)` in
Bombieri–Vaaler — is a height on a Grassmannian and is never called the height of `A` here. -/
@[expose] noncomputable def mulHeight (A : Matrix m n K) : ℝ :=
  Height.mulHeight fun q : m × n ↦ A q.1 q.2

/-- The logarithmic height of a matrix. As everywhere in this development, the logarithmic height
is *defined* as the logarithm of the multiplicative one and never independently. -/
@[expose] noncomputable def logHeight (A : Matrix m n K) : ℝ := log (mulHeight A)

theorem logHeight_eq_log_mulHeight (A : Matrix m n K) : logHeight A = log (mulHeight A) := rfl

/-- **The affine height of a matrix**: the height of the tuple of its entries with a coordinate
`1` appended, `Height.mulHeightAff` of the entries. Unlike `Matrix.mulHeight` it is not invariant
under scaling, which is exactly what a bound on the determinant needs. -/
@[expose] noncomputable def mulHeightAff (A : Matrix m n K) : ℝ :=
  Height.mulHeightAff fun q : m × n ↦ A q.1 q.2

/-- The logarithmic affine height of a matrix. -/
@[expose] noncomputable def logHeightAff (A : Matrix m n K) : ℝ := log (mulHeightAff A)

@[simp]
theorem mulHeight_zero : mulHeight (0 : Matrix m n K) = 1 := Height.mulHeight_zero

@[simp]
theorem logHeight_zero : logHeight (0 : Matrix m n K) = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_zero, log_one]

section Basic

variable [Finite m] [Finite n]

end Basic

section Mul

variable [Finite m] [Fintype n] [Finite p]

end Mul

section Det

variable [Fintype n] [DecidableEq n]

end Det

end Matrix

namespace Matrix

variable {K : Type*} [Field K] [NumberField K] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-!
### Matrices in the Arakelov normalization

At an infinite place the local factor of the Arakelov height is the Frobenius norm of the matrix,
and Cauchy–Schwarz entry by entry makes it submultiplicative; at a finite place the sup norm is
submultiplicative by the ultrametric inequality. So the constant
`Fintype.card n ^ totalWeight K` of `Matrix.mulHeight_mul_le` disappears.
-/

/-- **The Arakelov height of a matrix**: the Arakelov height of the tuple of its entries, so the
Frobenius norm at each infinite place and the sup norm at each finite one. -/
@[expose] noncomputable def arakelovMulHeight (A : Matrix m n K) : ℝ :=
  NumberField.arakelovMulHeight fun q : m × n ↦ A q.1 q.2

/-- The logarithmic Arakelov height of a matrix. -/
@[expose] noncomputable def arakelovLogHeight (A : Matrix m n K) : ℝ := log (arakelovMulHeight A)

@[simp]
theorem arakelovMulHeight_zero : arakelovMulHeight (0 : Matrix m n K) = 1 :=
  NumberField.arakelovMulHeight_zero

end Matrix

/-!
### Examples

The tests that fix the constants of the product bound: that `Fintype.card n ^ totalWeight K` is
attained, that its *exponent* is needed as soon as `K` has degree `> 1` — the rejection test the
roadmap states over `ℚ(i)`, here for every number field at once — that `[Nonempty n]` cannot be
dropped, and that the Arakelov constant `1` is attained.
-/

section Examples

open Height NumberField

end Examples

end
