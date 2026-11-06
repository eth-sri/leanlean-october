/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/

import ArithmeticHeights.Absolute
import Mathlib.NumberTheory.NumberField.House
import Mathlib.NumberTheory.SiegelsLemma

/-!
# Siegel's lemma, in height form

Mathlib proves the classical Siegel lemma as a statement about the **sup norm**: a nonzero
`M × N` integer matrix with `M < N` kills a nonzero integer vector of norm at most
`(N ‖A‖) ^ (M / (N - M))`. This file restates it in the vocabulary of heights, which is what the
rest of the roadmap consumes; the translation between the two normalizations is isolated as a
lemma of its own, the exponent is shown to be sharp, and the number-field corollary is read off
Mathlib's `house`-normalized version the same way.

## Main results

* `Rat.gcd_mul_mulHeight_intCast`: the translation. For a nonzero integer tuple,
  `gcd x * H(x) = max i, |x i|`; `Rat.mulHeight_intCast_le` is the inequality it is used through.
* `Int.Matrix.exists_ne_zero_mulVec_eq_zero_iSup_abs_le` and
  `Int.Matrix.exists_ne_zero_mulVec_eq_zero_mulHeight_le`: Siegel's lemma with an explicit bound
  `B` on the entries, in the sup norm and in the height, both at `(N B) ^ (M / (N - M))`.
* `Int.Matrix.exists_forall_pow_le_iSup_abs`: the exponent `M / (N - M)` is sharp.
* `NumberField.absMulHeight_le_iSup_house`: the absolute height of a tuple of algebraic integers
  is at most the largest house of its entries.
* `NumberField.exists_forall_exists_ne_zero_mulVec_eq_zero_absMulHeight_le`: Siegel's lemma over a
  number field in height form, Bombieri–Gubler's Corollary 2.9.2.

## Implementation notes

⚠ **The height form is not a strengthening, because the content can always be divided out.** The
height of an integer tuple is its sup norm divided by the greatest common divisor of its entries,
so `H(x) ≤ max i, |x i|` with equality exactly on primitive tuples. That makes the height bound
formally weaker-looking hypotheses and formally stronger conclusions, but nothing is gained: the
primitive multiple of a kernel vector is again a kernel vector, and it is the one on which the two
statements coincide. What the translation buys is the *vocabulary*: everything downstream of
Layer 1 is stated for `Height.mulHeight`, and a sup norm cannot be fed to it.

⚠ **The exponent is sharp already at `N = M + 1`, and only the factor `N ^ (M / (N - M))` is
slack.** The equations `B xᵢ = xᵢ₊₁` have kernel the line through `(1, B, B², …, B ^ M)`, whose
nonzero integer points all have sup norm at least `B ^ M`, against the bound `((M + 1) B) ^ M`.
Taking `k` such blocks side by side realizes every exponent `M = k M / (k (M + 1) - k M)`, so the
sharpness is not an artifact of `N - M = 1`. The bound is nevertheless not *invariant*: it changes
under `A ↦ U A` for `U ∈ GL_M(ℤ)`, which leaves the kernel alone, and removing that defect is the
whole content of Layer 5.2.

⚠ **Passing from the house to the height costs no constant at all.** For a tuple of algebraic
integers every finite local factor is at most `1` — the finite part of the height is the inverse
norm of the ideal the entries generate, and that norm is a positive integer — while each infinite
place is the modulus of a conjugate and so is dominated by the house. The infinite factors carry
the weights `mult v`, which sum to `[K : ℚ]`, and that is exactly the root the absolute
normalization takes. So `H_abs(x) ≤ max l, house (x l)` with no degree factor, and Mathlib's
number-field Siegel bound transfers verbatim.

⚠ **Mathlib's number-field constant is `private`.** `c₁ K` of
`Mathlib/NumberTheory/NumberField/House.lean` cannot be named from outside that file, so the
restatement has to quantify over it existentially — which is also the shape Bombieri–Gubler state
the corollary in — and the witness is supplied by unification against the theorem it is proved
from.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Lemma 2.9.1 and Corollary 2.9.2.

M. Hindry and J. H. Silverman, *Diophantine Geometry: An Introduction*, Springer (2000),
Lemma D.4.1, which is the statement Mathlib's file is proved against.

This is Layer 5.1 of the `ArithmeticHeights` roadmap.
-/

open Finset Height Matrix

/-! ### The sup norm of an integer tuple -/

/-! ### Siegel's lemma in height form -/

attribute [local instance] Matrix.seminormedAddCommGroup

/-! ### Siegel's lemma over a number field -/

