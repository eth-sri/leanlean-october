/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Hypergeom.ODE.ParameterSeriesDerivativeBounds
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-! Topology of the nonresonant parameter domain for Gauss connection coefficients. -/

@[expose] public section

namespace DOZZ.Proofs

/-- Parameter triples for which both local exponents in the connection problem are
nonresonant. -/
def gaussConnectionParameterDomain : Set (ℂ × ℂ × ℂ) :=
  {p | (∀ n : ℤ, p.2.2 ≠ (n : ℂ)) ∧
    ∀ n : ℤ, p.2.2 - p.1 - p.2.1 ≠ (n : ℂ)}

end DOZZ.Proofs
