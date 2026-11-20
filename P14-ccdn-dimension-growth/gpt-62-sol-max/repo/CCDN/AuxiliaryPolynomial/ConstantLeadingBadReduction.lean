/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateTotalDegree
public import CCDN.Noether.ClosedFormHeight
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import CCDN.Determinant.ClosedFormIntegerMinor
import CCDN.Determinant.ClosedFormMinorCharge
import CCDN.ForMathlib.Matrix
import CCDN.Noether.ClosedFormScaling

/-! Bad reduction for integer bivariate equations with a nonzero constant
outer leading coefficient. A leading-coefficient factor in the witness also
covers degree-dropping reductions. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial Real

/-- Full outer degree forces the outer leading coefficient to be constant. -/
lemma bivariate_leadingCoeff_eq_constant {R : Type*} [CommRing R]
    (f : R[X][X]) (htotal : bivariateTotalDegree f ≤ f.natDegree) :
    f.leadingCoeff = C (f.leadingCoeff.coeff 0) := by
  by_cases hc : f.leadingCoeff = 0
  simp_all
  have hn :=
    Polynomial.leadingCoeff_ne_zero.mpr hc
  have h := bivariateTotalDegree_coeff_le f f.natDegree f.leadingCoeff.natDegree hn
  exact eq_C_of_natDegree_eq_zero (by omega)

end
end CCDN
