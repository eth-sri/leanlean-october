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

/-- The inner and outer derivatives of a bivariate polynomial commute. -/
lemma derivative_bivariateCoefficientDerivative {F : Type*} [Field F] (p : F[X][X]) :
    ((bivariateCoefficientDerivative F) p).derivative =
      (bivariateCoefficientDerivative F) p.derivative := by
  ext n
  simp [coeff_derivative, derivative_mul, mul_comm]

/-- The logarithmic differential of a factor gives a closed form for the
whole product after clearing its denominator. -/
theorem bivariate_factor_closed_form {F : Type*} [Field F] (g h : F[X][X]) :
    (bivariateCoefficientDerivative F) (h * g.derivative) * (g * h) -
      (h * g.derivative) * (bivariateCoefficientDerivative F) (g * h) =
    (h * (bivariateCoefficientDerivative F) g).derivative * (g * h) -
      (h * (bivariateCoefficientDerivative F) g) * (g * h).derivative := by
  simp only [Derivation.leibniz, smul_eq_mul, derivative_mul,
    derivative_bivariateCoefficientDerivative]
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
  have hdiv : g ∣ C (1 - a) * (h * g.derivative) :=
    ⟨C a * h.derivative, by
      simp only [derivative_mul, map_sub, map_one] at he ⊢; linear_combination he⟩
  have hcdiv : g ∣ C (1 - a) := (hgh.mul_right hgg).dvd_of_dvd_mul_right hdiv
  have hc : C (1 - a) = (0 : R[X]) := by
    by_contra hn
    exact (not_le_of_gt (degree_C_le.trans_lt hg)) (degree_le_of_dvd hcdiv hn)
  have ha : a = 1 :=
    (sub_eq_zero.mp (Polynomial.C_injective (show C (1 - a) = C (0 : R) by simpa using hc))).symm
  rw [ha, C_1, one_mul, derivative_mul] at he
  have hg0 : g ≠ 0 := fun h => by simp [h] at hg
  exact (mul_ne_zero hg0 hh) (by linear_combination -he)

/-- The repeated-factor construction works for every multiplicity at least
two, with no restriction on the characteristic or the multiplicity. -/
theorem bivariate_power_factor_closed_form {F : Type*} [Field F]
    (g h : F[X][X]) (k : ℕ) :
    (bivariateCoefficientDerivative F) (g ^ k * h * g.derivative) * (g ^ (k + 2) * h) -
      (g ^ k * h * g.derivative) * (bivariateCoefficientDerivative F) (g ^ (k + 2) * h) =
    (g ^ k * h * (bivariateCoefficientDerivative F) g).derivative * (g ^ (k + 2) * h) -
      (g ^ k * h * (bivariateCoefficientDerivative F) g) * (g ^ (k + 2) * h).derivative := by
  rw [show g ^ (k + 2) * h = g * g * (g ^ k * h) by rw [pow_add, pow_two]; ring]
  simp only [Derivation.leibniz, smul_eq_mul, derivative_mul,
    derivative_bivariateCoefficientDerivative]
  ring

/-- For a nonconstant separable `g` coprime to `h`, the numerator `g ^ k * h * g'` is not a
scalar multiple of the derivative of `g ^ (k + 2) * h`; cancellation exposes its extra pole. -/
theorem power_factor_numerator_not_scalar_gradient
    {R : Type*} [CommRing R] [IsDomain R] (g h : R[X]) (k : ℕ)
    (hg : 0 < g.degree) (hgh : IsCoprime g h) (hgg : IsCoprime g g.derivative)
    (a : R) : g ^ k * h * g.derivative ≠ C a * (g ^ (k + 2) * h).derivative := by
  intro he
  have hg0 : g ≠ 0 := fun h => by simp [h] at hg
  have hd : (g ^ (k + 2) * h).derivative =
      g ^ k * (g * (C ((k + 2 : ℕ) : R) * g.derivative * h + g * h.derivative)) := by
    rw [derivative_mul, derivative_pow]
    simp only [show k + 2 - 1 = k + 1 by omega, pow_add, pow_one, pow_two]; ring
  rw [hd] at he
  have he' : h * g.derivative = C a * (g *
      (C ((k + 2 : ℕ) : R) * g.derivative * h + g * h.derivative)) :=
    mul_left_cancel₀ (pow_ne_zero k hg0) (by linear_combination he)
  have hunit := (hgh.mul_right hgg).isUnit_of_dvd
    (he'.symm ▸ dvd_mul_of_dvd_right (dvd_mul_right _ _) _)
  exact lt_irrefl _ (degree_eq_zero_of_isUnit hunit ▸ hg)

end
end CCDN
