/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import CCDN.Noether.BivariateCoefficientMatrix

/-! Explicit closed forms from polynomial factors, including repeated factors.
These supply reducibility obstructions for the differential matrix. -/

@[expose] public section
namespace CCDN
noncomputable section
open Polynomial

/-- The inner and outer derivatives of a bivariate polynomial commute. -/
lemma derivative_bivariateCoefficientDerivative {F : Type*} [Field F] (p : F[X][X]) :
    ((bivariateCoefficientDerivative F) p).derivative =
      (bivariateCoefficientDerivative F) p.derivative := by
  ext n
  simp [coeff_derivative]

/-- Clearing `g^m` in the closed differential `dg/g^m` gives a closed numerator pair. -/
theorem bivariate_factor_closed_form {F : Type*} [Field F] (g h : F[X][X]) (m : ℕ) :
    closedFormOperator (g ^ m * h) (h * g.derivative, h * (bivariateCoefficientDerivative F) g) = 0 := by
  change _ - _ - _ + _ = (0 : F[X][X])
  simp only [Derivation.leibniz, Derivation.leibniz_pow, nsmul_eq_mul, smul_eq_mul,
    derivative_mul, derivative_pow, derivative_bivariateCoefficientDerivative, C_eq_natCast]
  ring

/-- For coprime factors with a separable first factor and nonzero second
 derivative, the factor's logarithmic numerator cannot be a scalar multiple
 of the derivative of the product. This works in any characteristic. -/
theorem factor_numerator_not_scalar_gradient
    {R : Type*} [CommRing R] [IsDomain R] (g h : R[X])
    (hg : 0 < g.degree) (hgh : IsCoprime g h) (hgg : IsCoprime g g.derivative)
    (hh : h.derivative ≠ 0) (a : R) :
    h * g.derivative ≠ C a * (g * h).derivative := by
  intro he
  have hdiv : g ∣ C (1 - a) * (h * g.derivative) := by
    refine ⟨C a * h.derivative, ?_⟩
    grind [derivative_mul]
  have hcdiv := (hgh.mul_right hgg).dvd_of_dvd_mul_right hdiv
  have hc : C (1 - a) = (0 : R[X]) := by
    by_contra hn
    exact not_le_of_gt (LE.le.trans_lt degree_C_le hg) (degree_le_of_dvd hcdiv hn)
  have ha : a = 1 := by
    grind
  rw [ha, C_1, one_mul, derivative_mul] at he
  have hz : g * h.derivative = 0 := by linear_combination -he
  simp_all

end
end CCDN
