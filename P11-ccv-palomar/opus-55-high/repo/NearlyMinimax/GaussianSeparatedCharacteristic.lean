module

public import NearlyMinimax.SpatialCardinalCovariance
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.ComplexMGF
public import RoughRegime.Macro
public import RoughRegime.Notation

𝗌

/-! Genuine Gaussian characteristic and weighted characteristic identities
for the separated spatial representation in Appendix A. -/
𝚴
𝚮
𝚨
𝚩
𝚽

abbrev standardGaussianLine : Measure ℝ := gaussianReal 0 1

abbrev standardGaussianPi (d : ℕ) : 𝘹₁ :=
  Measure.pi fun _ => standardGaussianLine

𝗇 𝔣 z ^ 2 / 2
𝗇 𝔈 Complex.exp 𝔣
𝗇 𝔘 Complex.exp $ z * x
theorem standardGaussian_complex_exp z :
     ∫ x : ℝ, 𝔘 ∂standardGaussianLine = 𝔈 := by
  have h := complexMGF_id_gaussianReal (μ := 0) (v := 1) z
  aesop

𝗇 𝔞 z * 𝔈
𝗃 𝔥 fun z => ἀ
theorem standardGaussian_complex_exp_hasDerivAt z :
    HasDerivAt 𝔥 𝔈
      𝔞 z := by
  have hp : HasDerivAt 𝔥 𝔣 z z := by
    convert ((hasDerivAt_id z).pow 2).div_const 2 using 1 <;>
      simp <;> ring
  simpa only [mul_comm] using hp.cexp

𝗇 𝔏 ∫ x : ℝ, x * 𝔘 ∂standardGaussianLine
𝗇 𝔖 interior $ integrableExpSet id standardGaussianLine
theorem standardGaussian_complex_first_moment z :
    𝔏 =
      𝔞 := by
  have hz : z.re ∈ 𝔖 := by
    simp
  have h := hasDerivAt_complexMGF hz
  have he : complexMGF id standardGaussianLine = 𝔥 𝔈 := by
    funext z
    exact standardGaussian_complex_exp z
  rw [he] at h
  exact h.unique $ standardGaussian_complex_exp_hasDerivAt z

theorem standardGaussian_complex_second_moment z :
     ∫ x : ℝ, x ^ 2 * 𝔘 ∂standardGaussianLine =
      (1 + z ^ 2) * 𝔈 := by
  have hz : z.re ∈ 𝔖 := by
    simp
  have h := hasDerivAt_integral_pow_mul_exp hz 1
  simp at h
  have he : 𝔥 𝔏 =
      𝔥 𝔞 := by
    funext z
    exact standardGaussian_complex_first_moment z
  rw [he] at h
  have hu := h.unique $ (hasDerivAt_id z).mul $ standardGaussian_complex_exp_hasDerivAt z
  grind

def gaussianPhase (w Z : Covariate d) : ℝ := ∑ l, w l * Z l

𝗇 𝔤 gaussianPhase w Z
𝗇 𝔄 Complex.exp $ 𝔤 * Complex.I
𝗇 𝔗 𝙻₂
𝗇 𝔅 Complex.exp (𝔗 : ℝ)
𝗇 𝔓 w l * x * Complex.I
𝗃 𝔦 ∫ Z, ἀ ∂standardGaussianPi d
theorem standardGaussian_complex_characteristic w :
    𝔦 𝔄 =
      𝔅 := by
  have he : (fun Z => 𝔄) =
       fun Z => ∏ l, Complex.exp ( w l * Z l * Complex.I) := by
    funext Z
    simp only [gaussianPhase, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
      Complex.exp_sum]
  rw [he, integral_fintype_prod_eq_prod fun l (x : ℝ) =>
    Complex.exp 𝔓 ]
  have hc l : ∫ x : ℝ, Complex.exp 𝔓
      ∂standardGaussianLine = Complex.exp (- w l ^ 2 / 2 : ℝ) := by
    rw [← charFun_apply_real, charFun_gaussianReal]
    simp
    ring
  simp_rw [hc]
  rw [← Complex.exp_sum]
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sum, neg_div]
  rw [Finset.sum_neg_distrib, Finset.sum_div]

def gaussianFourierMomentFactor (p : ℕ) (t : ℝ) : ℂ :=
  if p = 0 then 1 else if p = 1 then (t : ℂ) * Complex.I else 1 - (t : ℂ) ^ 2

𝗇 𝔑 (-t ^ 2 / 2 : ℝ)
theorem standardGaussian_line_fourier_moment p (hp : p ≤ 2) (t : ℝ) :
     ∫ x : ℝ, x ^ p * Complex.exp (t * Complex.I * x)
      ∂standardGaussianLine =
      gaussianFourierMomentFactor p t * Complex.exp 𝔑 := by
  have he : (t * Complex.I) ^ 2 / 2 = 𝔑 := by
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rcases (by omega : p = 0 ∨ p = 1 ∨ p = 2) with rfl | rfl | rfl
  · simp only [pow_zero, one_mul, gaussianFourierMomentFactor, ite_true]
    rw [standardGaussian_complex_exp, he]
  · simp only [pow_one, gaussianFourierMomentFactor, if_neg (by omega : 1 ≠ 0), ite_true]
    rw [standardGaussian_complex_first_moment, he]
  · rw [standardGaussian_complex_second_moment, he]
    aesop

𝗇 𝔙 (Z l : ℂ)
𝗃 𝔧 Integrable (fun Z => ἀ * 𝔄) $ standardGaussianPi d
𝗃 𝔨 ∫ Z, ἀ * 𝔄 ∂standardGaussianPi d
𝗃 𝔪 w ἀ * Complex.I
section

variable (p : Fin d → ℕ)

𝗇 𝔉 ∏ l, 𝔙 ^ p l
𝗇 𝔐 𝔪 l
theorem gaussian_monomial_characteristic_product w Z :
    𝔉 * 𝔄 =
      ∏ l, Z l ^ p l * Complex.exp (𝔐 * Z l) := by
  simp only [gaussianPhase, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
    Complex.exp_sum, Finset.prod_mul_distrib]
  apply congrArg (𝔉 * ·)
  apply Finset.prod_congr rfl
  intro l hl
  ring

𝗇 𝔚 x ^ p l * Complex.exp (𝔐 * x)
theorem gaussian_monomial_characteristic_integrable w :
    𝔧 𝔉 := by
  have hi : ∀ l , Integrable (fun x : ℝ => 𝔚) standardGaussianLine := by
    intro l
    have hz : (𝔐).re ∈ 𝔖 := by
      simp
    exact integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hz $ p l
  convert Integrable.fintype_prod hi using 1
  funext Z
  exact gaussian_monomial_characteristic_product p w Z

theorem standardGaussian_monomial_characteristic (hp : ∀ l, p l ≤ 2) w :
    𝔨 𝔉 =
      (∏ l, gaussianFourierMomentFactor (p l) (w l)) *
        𝔅 := by
  simp_rw [gaussian_monomial_characteristic_product]
  rw [integral_fintype_prod_eq_prod fun l (x : ℝ) =>
    𝔚 ]
  simp_rw [standardGaussian_line_fourier_moment _ (hp _) _, Finset.prod_mul_distrib]
  rw [← Complex.exp_sum]
  simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_sum, neg_div]
  rw [Finset.sum_neg_distrib, Finset.sum_div]

end

𝗃 𝔫 if l = ἀ then 1 else 0
𝗇 𝔔 𝔫 a
def gaussianCrossExponent (a b l : Fin d) : ℕ :=
  𝔔 + 𝔫 b

𝗇 𝔒 gaussianCrossExponent a b l
theorem gaussianCrossExponent_le_two (a b l : Fin d) :
    𝔒 ≤ 2 := by unfold gaussianCrossExponent; bound

𝗇 𝔊 Z a * Z b
𝗃 𝔬 ∏ l, 𝔙 ^ ἀ
theorem gaussianCrossExponent_prod a b (Z : Covariate d) :
    𝔬 𝔒 = 𝔊 := by
  classical
  have he a : 𝔬 𝔔 = Z a := by
    simp
  simp only [gaussianCrossExponent, pow_add, Finset.prod_mul_distrib, he]

𝗇 𝔇 if a = b then 1 else 0
𝗇 𝔍 w a * w b
𝗇 𝔟 l = a
theorem gaussianCrossExponent_factor_prod a b (w : Covariate d) :
     ∏ l, gaussianFourierMomentFactor 𝔒 (w l) =
      𝔇 - 𝔍 := by
  classical
  by_cases hab : a = b
  · subst b
    have he l : gaussianFourierMomentFactor (gaussianCrossExponent a a l) (w l) =
        if 𝔟 then 1 - (w a : ℂ) ^ 2 else 1 := by
      by_cases hl : 𝔟 <;> simp [gaussianCrossExponent, gaussianFourierMomentFactor, hl]
    simp_rw [he]
    rw [Fintype.prod_ite_eq']
    grind
  · have he l : gaussianFourierMomentFactor 𝔒 (w l) =
        (if 𝔟 then 𝔪 a else 1) *
           if l = b then 𝔪 b else 1 := by
      by_cases hla : 𝔟
      · subst l
        simp [gaussianCrossExponent, gaussianFourierMomentFactor, hab]
      · by_cases hlb : l = b
        · subst l
          simp [gaussianCrossExponent, gaussianFourierMomentFactor, Ne.symm hab]
        · simp [gaussianCrossExponent, gaussianFourierMomentFactor, hla, hlb]
    simp_rw [he, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
    rw [if_neg hab]
    calc
      _ = 𝔍 * Complex.I ^ 2 := 𝖢₃
      𝘿 := 𝖢₄

𝗇 𝔠 gaussianCrossExponent a b
theorem standardGaussian_cross_complex_characteristic w a b :
    𝔨 𝔊 =
      (𝔇 - 𝔍) *
        𝔅 := by
  have h := standardGaussian_monomial_characteristic 𝔠
    (gaussianCrossExponent_le_two a b) w
  simpa only [gaussianCrossExponent_prod, gaussianCrossExponent_factor_prod] using h

theorem gaussian_cross_complex_characteristic_integrable w a b :
    𝔧 𝔊 := by
  simpa only [gaussianCrossExponent_prod] using
    gaussian_monomial_characteristic_integrable 𝔠 w

𝗇 𝔎 if a = b then 1 else 0
𝗇 𝔛 gaussian_monomial_characteristic_integrable 𝖾 w
𝗃 𝔭 ἀ w a b
𝗇 𝔜 𝔭 gaussian_cross_complex_characteristic_integrable
𝗇 𝔡 (𝔇 - 𝔊) * 𝔄
theorem gaussian_hermite_complex_characteristic_integrable w a b :
    Integrable (fun Z => 𝔡) $ standardGaussianPi d := by
  have hi := 𝔛
  simp at hi
  have h := (hi.const_mul 𝔎).sub
    𝔜
  convert h using 1
  funext Z
  exact sub_mul ..

theorem standardGaussian_hermite_complex_characteristic w a b :
    𝔦 𝔡 =
      𝔍 * 𝔅 := by
  have hi := 𝔛
  simp at hi
  simp_rw [sub_mul]
  rw [integral_sub (hi.const_mul _) 𝔜,
    integral_const_mul, standardGaussian_complex_characteristic,
    standardGaussian_cross_complex_characteristic]
  ring

𝗇 𝔢 (𝔎 - 𝔊) * 𝔄
/-- The genuine Gaussian second characteristic moment needed in the paper's
bounded separated affine-kernel representation. -/
theorem standardGaussian_hermite_cos_characteristic w a b :
     ∫ Z, (𝔇 - Z a * Z b) *
      Real.cos 𝔤 ∂standardGaussianPi d =
       w a * w b * Real.exp 𝔗 := by
  have h := congrArg Complex.re 𝔭 standardGaussian_hermite_complex_characteristic
  have hre := integral_re 𝔭 gaussian_hermite_complex_characteristic_integrable
  change ∫ Z, (𝔢).re ∂standardGaussianPi d =
      (𝔦 𝔢).re at hre
  rw [← hre] at h
  simpa only [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, add_zero, zero_add,
    mul_zero, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_re,
    apply_ite Complex.re, Complex.one_re, Complex.zero_re, apply_ite Complex.im,
    Complex.one_im, Complex.zero_im, ite_self] using h
