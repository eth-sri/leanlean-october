module

public import NearlyMinimax.SpatialCardinalCovariance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.ComplexMGF

@[expose] public section

/-! Genuine Gaussian characteristic and weighted characteristic identities
for the separated spatial representation in Appendix A. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

abbrev standardGaussianLine : Measure ℝ := gaussianReal 0 1

abbrev standardGaussianPi (d : ℕ) : Measure (Covariate d) :=
  Measure.pi (fun _ => standardGaussianLine)

variable {d : ℕ} (z : ℂ) (p : Fin d → ℕ) (w : Covariate d) (a b : Fin d)

theorem standardGaussian_complex_exp :
    (∫ x, Complex.exp (z * x) ∂standardGaussianLine) = Complex.exp (z ^ 2 / 2) := by
  simpa only [complexMGF, id_eq, Complex.ofReal_zero, mul_zero, NNReal.coe_one,
    Complex.ofReal_one, one_mul, zero_add] using complexMGF_id_gaussianReal (μ := 0) (v := 1) z

theorem standardGaussian_complex_exp_hasDerivAt :
    HasDerivAt (fun z => Complex.exp (z ^ 2 / 2))
      (z * Complex.exp (z ^ 2 / 2)) z := by
  have hp : HasDerivAt (fun z => z ^ 2 / 2) z z := by
    convert ((hasDerivAt_id z).pow 2).div_const 2 using 1 <;>
      simp <;> ring
  simpa only [mul_comm] using hp.cexp

theorem standardGaussian_complex_first_moment :
    (∫ x, x * Complex.exp (z * x) ∂standardGaussianLine) =
      z * Complex.exp (z ^ 2 / 2) := by
  have hz : z.re ∈ interior (integrableExpSet id standardGaussianLine) := by
    simp
  have h := hasDerivAt_complexMGF hz
  have he : complexMGF id standardGaussianLine = fun z => Complex.exp (z ^ 2 / 2) := by
    funext z
    exact standardGaussian_complex_exp z
  rw [he] at h
  exact h.unique (standardGaussian_complex_exp_hasDerivAt z)

theorem standardGaussian_complex_second_moment :
    (∫ x, x ^ 2 * Complex.exp (z * x) ∂standardGaussianLine) =
      (1 + z ^ 2) * Complex.exp (z ^ 2 / 2) := by
  have hz : z.re ∈ interior (integrableExpSet id standardGaussianLine) := by
    simp
  have h := hasDerivAt_integral_pow_mul_exp hz 1
  simp at h
  have he : (fun z => ∫ x, x * Complex.exp (z * x) ∂standardGaussianLine) =
      (fun z => z * Complex.exp (z ^ 2 / 2)) := by
    funext z
    exact standardGaussian_complex_first_moment z
  rw [he] at h
  exact (h.unique ((hasDerivAt_id z).mul (standardGaussian_complex_exp_hasDerivAt z))).trans (by simp; ring)

def gaussianPhase (Z : Covariate d) : ℝ := ∑ l, w l * Z l

theorem standardGaussian_complex_characteristic :
    (∫ Z, Complex.exp ((gaussianPhase w Z) * Complex.I) ∂standardGaussianPi d) =
      Complex.exp (-(∑ l, (w l) ^ 2) / 2 : ℝ) := by
  have he : (fun Z => Complex.exp ((gaussianPhase w Z) * Complex.I)) =
      (fun Z => ∏ l, Complex.exp ((w l) * Z l * Complex.I)) := by
    simp only [gaussianPhase, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
      Complex.exp_sum]
  rw [he, integral_fintype_prod_eq_prod (fun l (x : ℝ) =>
    Complex.exp ((w l) * x * Complex.I))]
  have hc l : (∫ x, Complex.exp ((w l) * x * Complex.I)
      ∂standardGaussianLine) = Complex.exp (-(w l) ^ 2 / 2) := by
    rw [← charFun_apply_real, charFun_gaussianReal]
    simp
    ring
  simp_rw [hc]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.ofReal_sum, neg_div]
  rw [Finset.sum_neg_distrib, Finset.sum_div]

def gaussianFourierMomentFactor (p : ℕ) (t : ℝ) : ℂ :=
  if p = 0 then 1 else if p = 1 then t * Complex.I else 1 - t ^ 2

theorem standardGaussian_line_fourier_moment {p : ℕ} (hp : p ≤ 2) (t : ℝ) :
    (∫ x, x ^ p * Complex.exp (t * Complex.I * x)
      ∂standardGaussianLine) =
      gaussianFourierMomentFactor p t * Complex.exp (-t ^ 2 / 2 : ℝ) := by
  have he : (t * Complex.I) ^ 2 / 2 = (-t ^ 2 / 2 : ℝ) := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl
  · simp only [pow_zero, one_mul, gaussianFourierMomentFactor, ite_true]
    rw [standardGaussian_complex_exp, he]
  · simp only [pow_one, gaussianFourierMomentFactor, if_neg (by omega : 1 ≠ 0), ite_true]
    rw [standardGaussian_complex_first_moment, he]
  · simp only [gaussianFourierMomentFactor, if_neg (by omega : 2 ≠ 0), if_neg (by omega : 2 ≠ 1)]
    rw [standardGaussian_complex_second_moment, he]
    congr 1
    rw [mul_pow, Complex.I_sq]
    ring

theorem gaussian_monomial_characteristic_product (Z : Covariate d) :
    (∏ l, (Z l : ℂ) ^ p l) * Complex.exp ((gaussianPhase w Z) * Complex.I) =
      ∏ l, (Z l) ^ p l * Complex.exp ((w l) * Complex.I * Z l) := by
  simp only [gaussianPhase, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
    Complex.exp_sum, Finset.prod_mul_distrib]
  apply congrArg ((∏ l, (Z l : ℂ) ^ p l) * ·)
  apply Finset.prod_congr rfl
  intro l hl
  ring

theorem gaussian_monomial_characteristic_integrable :
    Integrable (fun Z => (∏ l, (Z l : ℂ) ^ p l) *
      Complex.exp ((gaussianPhase w Z) * Complex.I)) (standardGaussianPi d) := by
  have hi : ∀ l, Integrable (fun x : ℝ => x ^ p l *
      Complex.exp ((w l) * Complex.I * x)) standardGaussianLine := fun l => integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet (by
      simp) (p l)
  convert (Integrable.fintype_prod hi) using 1
  funext Z
  exact gaussian_monomial_characteristic_product ..

theorem standardGaussian_monomial_characteristic {p : Fin d → ℕ}
    (hp : ∀ l, p l ≤ 2) (w : Covariate d) :
    (∫ Z, (∏ l, (Z l : ℂ) ^ p l) * Complex.exp ((gaussianPhase w Z) * Complex.I)
      ∂standardGaussianPi d) =
      (∏ l, gaussianFourierMomentFactor (p l) (w l)) *
        Complex.exp (-(∑ l, (w l) ^ 2) / 2 : ℝ) := by
  simp_rw [gaussian_monomial_characteristic_product]
  rw [integral_fintype_prod_eq_prod (fun l (x : ℝ) =>
    x ^ p l * Complex.exp ((w l) * Complex.I * x))]
  simp_rw [standardGaussian_line_fourier_moment (hp _) _, Finset.prod_mul_distrib]
  apply congrArg ((∏ l, gaussianFourierMomentFactor (p l) (w l)) * ·)
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat,
    Complex.ofReal_sum, neg_div]
  rw [Finset.sum_neg_distrib, Finset.sum_div]

def gaussianCrossExponent (l : Fin d) : ℕ :=
  (if l = a then 1 else 0) + (if l = b then 1 else 0)

theorem gaussianCrossExponent_le_two (l : Fin d) :
    gaussianCrossExponent a b l ≤ 2 := by unfold gaussianCrossExponent; split_ifs <;> omega

theorem gaussianCrossExponent_prod (Z : Covariate d) :
    (∏ l, (Z l : ℂ) ^ gaussianCrossExponent a b l) = (Z a) * Z b := by
  classical
  have he a : (∏ l, (Z l : ℂ) ^ (if l = a then 1 else 0)) = Z a := by
    simp
  simp only [gaussianCrossExponent, pow_add, Finset.prod_mul_distrib, he]

theorem gaussianCrossExponent_factor_prod (w : Covariate d) :
    (∏ l, gaussianFourierMomentFactor (gaussianCrossExponent a b l) (w l)) =
      (if a = b then 1 else 0) - (w a) * w b := by
  classical
  by_cases hab : a = b
  · subst b
    simp [gaussianCrossExponent, gaussianFourierMomentFactor] <;> ring
  · have he l : gaussianFourierMomentFactor (gaussianCrossExponent a b l) (w l) =
        (if l = a then (w a) * Complex.I else 1) *
          (if l = b then (w b) * Complex.I else 1) := by
      grind [gaussianCrossExponent, gaussianFourierMomentFactor]
    simp_rw [he, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    rw [if_neg hab]
    calc
      _ = (w a) * w b * Complex.I ^ 2 := by ring
      _ = _ := by simp

theorem standardGaussian_cross_complex_characteristic :
    (∫ Z, ((Z a) * Z b) * Complex.exp ((gaussianPhase w Z) * Complex.I)
      ∂standardGaussianPi d) =
      ((if a = b then 1 else 0) - (w a) * w b) *
        Complex.exp (-(∑ l, (w l) ^ 2) / 2 : ℝ) := by
  simpa only [gaussianCrossExponent_prod, gaussianCrossExponent_factor_prod] using standardGaussian_monomial_characteristic (gaussianCrossExponent_le_two a b) w

theorem gaussian_cross_complex_characteristic_integrable :
    Integrable (fun Z => ((Z a) * Z b) *
      Complex.exp ((gaussianPhase w Z) * Complex.I)) (standardGaussianPi d) := by
  simpa only [gaussianCrossExponent_prod] using
    gaussian_monomial_characteristic_integrable (gaussianCrossExponent a b) w

theorem gaussian_hermite_complex_characteristic_integrable :
    Integrable (fun Z => ((if a = b then 1 else 0) - (Z a) * Z b) *
      Complex.exp ((gaussianPhase w Z) * Complex.I)) (standardGaussianPi d) := by
  have hi := gaussian_monomial_characteristic_integrable (fun _ => 0) w
  simp at hi
  have h := (hi.const_mul (if a = b then 1 else 0)).sub
    (gaussian_cross_complex_characteristic_integrable w a b)
  convert h using 1
  exact sub_mul ..

theorem standardGaussian_hermite_complex_characteristic :
    (∫ Z, ((if a = b then 1 else 0) - (Z a) * Z b) *
      Complex.exp ((gaussianPhase w Z) * Complex.I) ∂standardGaussianPi d) =
      ((w a) * w b) * Complex.exp (-(∑ l, (w l) ^ 2) / 2 : ℝ) := by
  have hi := gaussian_monomial_characteristic_integrable (fun _ => 0) w
  simp at hi
  simp_rw [sub_mul]
  rw [integral_sub (hi.const_mul _) (gaussian_cross_complex_characteristic_integrable ..),
    integral_const_mul, standardGaussian_complex_characteristic,
    standardGaussian_cross_complex_characteristic]
  ring

/-- The genuine Gaussian second characteristic moment needed in the paper's
bounded separated affine-kernel representation. -/
theorem standardGaussian_hermite_cos_characteristic :
    (∫ Z, ((if a = b then 1 else 0) - Z a * Z b) *
      Real.cos (gaussianPhase w Z) ∂standardGaussianPi d) =
      (w a * w b) * Real.exp (-(∑ l, (w l) ^ 2) / 2) := by
  have h := congrArg Complex.re (standardGaussian_hermite_complex_characteristic w a b)
  have hre := integral_re (gaussian_hermite_complex_characteristic_integrable w a b)
  change (∫ Z, (((if a = b then 1 else 0) - (Z a) * Z b) *
    Complex.exp ((gaussianPhase w Z) * Complex.I)).re ∂standardGaussianPi d) =
      (∫ Z, ((if a = b then 1 else 0) - (Z a) * Z b) *
        Complex.exp ((gaussianPhase w Z) * Complex.I) ∂standardGaussianPi d).re at hre
  rw [← hre] at h
  simpa only [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im,  zero_add,
    mul_zero, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_re,
    apply_ite Complex.re, Complex.one_re, Complex.zero_re, apply_ite Complex.im,
    Complex.one_im, Complex.zero_im, ite_self] using h

end NearlyMinimax
