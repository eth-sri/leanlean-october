/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

import CCDN.Algebra.IdealZeroLocus
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import CCDN.Height.PrimitivePairReconstruction
import Mathlib.Algebra.MvPolynomial.CommRing

/-! Birational projection coordinates admit a rational inverse in the original
coordinate ring. Its denominator cuts out all possible noninjective fibers.
This module gives no bound on the degree of that denominator;
`ExceptionalCount` converts a denominator of degree `D` into at most `d * D`
exceptional points. -/

namespace CCDN
section
open MvPolynomial

