/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateClosedForms

/-! Explicit closed forms from polynomial factors, including repeated factors.
These supply reducibility obstructions for the differential matrix. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

variable {F : Type*} [Field F] (g h : F[X][X]) {R : Type*} [CommRing R] [IsDomain R]

/-- The inner and outer derivatives of a bivariate polynomial commute. -/
lemma derivative_bivariateCoefficientDerivative (p : F[X][X]) :
    ((bivariateCoefficientDerivative F) p).derivative =
      (bivariateCoefficientDerivative F) p.derivative := by
  ext n
  simp [coeff_derivative, derivative_mul, mul_comm]

end
end CCDN
