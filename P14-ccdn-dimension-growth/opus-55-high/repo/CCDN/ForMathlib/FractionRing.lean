/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
# Fraction fields of localizations, polynomial rings and finite extensions

## Main results

* `IsFractionRing.liftOfLocalization`: a nonzero localization of a domain embeds compatibly in any
  fraction field of the domain, which is then a fraction field of the localization
  (`IsFractionRing.isFractionRing_liftOfLocalization`).
* `MvPolynomial.coeffFractionRingEmbedding`: a fraction field of a coefficient domain `A` embeds
  canonically in a fraction field of `MvPolynomial σ A`, compatibly with `A` and its ground field.
* `MvPolynomial.fractionRingCoeffMap`, `MvPolynomial.isFractionRing_fractionRingCoeffMap`:
  enlarging the coefficients to their fraction field does not change the fraction field of a
  polynomial ring.
* `IsFractionRing.exists_ne_zero_mul_mem_range_of_finite`: a finite extension of domains with a
  common fraction field has a nonzero conductor element.
-/

section

namespace IsFractionRing

