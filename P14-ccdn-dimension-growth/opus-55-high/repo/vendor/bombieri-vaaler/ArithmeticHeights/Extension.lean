/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/

import ArithmeticHeights.Arakelov
import Mathlib.RingTheory.Ideal.Norm.RelNorm

/-!
# Heights under a finite extension of number fields

Mathlib's `Height.mulHeight` is the height **relative** to the field it is computed over. This
file proves how it changes when that field grows: for a finite extension `L / K` of number
fields and a tuple `x` over `K`,

`mulHeight x ^ [L : K] = mulHeight (algebraMap K L ∘ x)`.

Equivalently, `mulHeight x ^ (finrank ℚ K)⁻¹` does not depend on the field the coordinates are
read in — the statement that the *absolute* height is well defined, recorded here for a single
element as `NumberField.absMulHeight₁_eq`.

## Main results

* `NumberField.mulHeight_pow_finrank` and `NumberField.mulHeight₁_pow_finrank`: the tuple and
  one-variable forms of the displayed identity.
* `NumberField.finrank_nsmul_logHeight` and `NumberField.finrank_nsmul_logHeight₁`: the
  logarithmic forms, where the power becomes an `nsmul`.
* `NumberField.absMulHeight₁_eq`: over *any* number field `K` containing it, the absolute height
  of `x` is `mulHeight₁ x ^ (finrank ℚ K : ℝ)⁻¹`. This is the classical statement that the
  absolute height does not depend on the field of definition, and
  `NumberField.absMulHeight₁_pow_finrank` is the same identity with a natural-number exponent.
  `NumberField.absLogHeight₁_eq` is its logarithmic form: the absolute logarithmic height is the
  relative one divided by the degree.

## Implementation notes

The two factors of the height are handled by different mechanisms, and neither is the
places-above-places bookkeeping one might expect.

The **archimedean** factor is first turned into a product over the complex embeddings — this is
what `InfinitePlace.card_filter_mk_eq` does, the exponent `mult v` being the number of embeddings
inducing `v`. The statement then becomes the count `#{φ : L →+* ℂ | φ.comp (algebraMap K L) = ψ}
= [L : K]`, which is `AlgHom.card` once `ℂ` carries the `K`-algebra structure of `ψ`. The
roadmap asks for `InfinitePlace.liesOver_iff_comap_eq` as the first step of this layer; it is not
needed on this route, and Mathlib meanwhile carries that theory itself, in
`Mathlib/NumberTheory/NumberField/InfinitePlace/Ramification.lean`.

The **nonarchimedean** factor of the height of an *integral* tuple is the inverse of the absolute
norm of the ideal its coordinates generate, by
`NumberField.absNorm_mul_finprod_finitePlace_eq_one`. So that half reduces to
`Ideal.absNorm (I.map (algebraMap (𝓞 K) (𝓞 L))) = Ideal.absNorm I ^ [L : K]`, which is
`Ideal.relNorm_algebraMap` followed by `Ideal.absNorm_relNorm` — no ramification or inertia
appears, since those are already inside Mathlib's relative ideal norm.

⚠ The nonarchimedean factor alone is **not** invariant under scaling: `∏ᶠ v, ⨆ i, v (c * x i)`
picks up the finite part of the product formula for `c`. The reduction from an arbitrary tuple to
an integral one is therefore performed on the whole height, where
`Height.mulHeight_smul_eq_mulHeight` applies to both sides at once, and not factor by factor.

## References

These are the statements of
[mathlib4#41606](https://github.com/leanprover-community/mathlib4/pull/41606) and carry its
names, so that adopting Mathlib's version is a deletion plus an import.

This is Layer 0.3 of the `ArithmeticHeights` roadmap.
-/

