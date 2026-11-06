/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Defs

/-! The zero locus of an ideal of multivariate polynomials, with coordinates in the
coefficient ring. Over a field `K` this is Mathlib's `MvPolynomial.zeroLocus K I`,
stated with `eval` rather than `aeval`; that definition is reserved for points with
coordinates in an extension field. -/

namespace CCDN
section
open MvPolynomial

/-- The common zeros, with coordinates in the coefficient ring, of all polynomials in `I`. -/
def idealZeroLocus {K σ : Type*} [CommRing K] (I : Ideal (MvPolynomial σ K)) : Set (σ → K) :=
  {x | ∀ f ∈ I, eval x f = 0}

