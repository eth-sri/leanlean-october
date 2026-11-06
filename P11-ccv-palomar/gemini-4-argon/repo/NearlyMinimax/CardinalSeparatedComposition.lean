module
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.ComplexMGF
public import NearlyMinimax.GaussianSpatialDomination
public import NearlyMinimax.ActualSeparatedPacket
public import Mathlib.MeasureTheory.Integral.Pi
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set MvPolynomial
open scoped BigOperators ENNReal
namespace NearlyMinimax
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
section
variable {d : ℕ}
abbrev standardGaussianLine : Measure ℝ := gaussianReal 0 1
abbrev standardGaussianPi (d ) : Measure (Covariate d) :=
  Measure.pi (fun _ => standardGaussianLine)
theorem standardGaussian_complex_exp (z ) :
    (∫ x : ℝ, Complex.exp (z * x) ∂standardGaussianLine) = Complex.exp (z ^ 2 / 2) := by
  simpa only [complexMGF, id_eq, Complex.ofReal_zero, mul_zero, NNReal.coe_one,
    Complex.ofReal_one, one_mul, zero_add] using (complexMGF_id_gaussianReal (μ := 0) (v := 1) z)
theorem standardGaussian_complex_exp_hasDerivAt (z ) :
    HasDerivAt (fun z => Complex.exp (z ^ 2 / 2))
      (z * Complex.exp (z ^ 2 / 2)) z := by
  have hp : HasDerivAt (fun z => z ^ 2 / 2) z z := by
    convert ((hasDerivAt_id z).pow 2).div_const 2 using 1 <;>
      simp only [Pi.pow_apply, id_eq] <;> ring
  simpa only [mul_comm] using hp.cexp
theorem standardGaussian_complex_first_moment (z : ℂ) :
    (∫ x : ℝ, x * Complex.exp (z * x) ∂standardGaussianLine) =
      z * Complex.exp (z ^ 2 / 2) := by
  have hz : z.re ∈ interior (integrableExpSet id standardGaussianLine) := by
    simp only [integrableExpSet_id_gaussianReal, interior_univ, mem_univ]
  have h := hasDerivAt_complexMGF hz
  have he : complexMGF id standardGaussianLine = fun z => Complex.exp (z ^ 2 / 2) := by
    funext z
    exact standardGaussian_complex_exp z
  rw [he] at h
  exact h.unique (standardGaussian_complex_exp_hasDerivAt z)
theorem standardGaussian_complex_second_moment (z : ℂ) :
    (∫ x : ℝ, x ^ 2 * Complex.exp (z * x) ∂standardGaussianLine) =
      (1 + z ^ 2) * Complex.exp (z ^ 2 / 2) := by
  have hz : z.re ∈ interior (integrableExpSet id standardGaussianLine) := by
    simp only [integrableExpSet_id_gaussianReal, interior_univ, mem_univ]
  have h := hasDerivAt_integral_pow_mul_exp hz 1
  simp only [id_eq, pow_one, Nat.reduceAdd] at h
  have he : (fun z => ∫ x : ℝ, x * Complex.exp (z * x) ∂standardGaussianLine) =
      (fun z => z * Complex.exp (z ^ 2 / 2)) := by
    funext z
    exact standardGaussian_complex_first_moment z
  rw [he] at h
  have hd := (hasDerivAt_id z).mul (standardGaussian_complex_exp_hasDerivAt z)
  have hu := h.unique hd
  exact hu.trans (by simp only [id_eq]; ring)
def gaussianPhase  (w Z : Covariate d) : ℝ := ∑ l, w l * Z l
def gaussianFourierMomentFactor (p : ℕ) (t : ℝ) : ℂ :=
  if p = 0 then 1 else if p = 1 then t * Complex.I else 1 - t ^ 2
theorem standardGaussian_line_fourier_moment (p ) (hp : p ≤ 2) (t : ℝ) :
    (∫ x : ℝ, ↑x ^ p * Complex.exp (↑t * Complex.I * x)
      ∂standardGaussianLine) =
      gaussianFourierMomentFactor p t * Complex.exp ((-t ^ 2 / 2 : ℝ) : ℂ) := by
  have he : (↑t * Complex.I) ^ 2 / 2 = ((-t ^ 2 / 2 : ℝ) : ℂ) := by
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
theorem gaussian_monomial_characteristic_product  (p : Fin d → ℕ)
    (w Z : Covariate d) :
    (∏ l, (Z l : ℂ) ^ p l) * Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I) =
      ∏ l, (Z l : ℂ) ^ p l * Complex.exp ((w l : ℂ) * Complex.I * Z l) := by
  simp only [gaussianPhase, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
    Complex.exp_sum, Finset.prod_mul_distrib]
  apply congrArg ((∏ l, (Z l : ℂ) ^ p l) * ·)
  apply Finset.prod_congr rfl
  intro l hl
  congr 1
  ring
theorem gaussian_monomial_characteristic_integrable  (p : Fin d → ℕ)
    (w : Covariate d) :
    Integrable (fun Z => (∏ l, (Z l : ℂ) ^ p l) *
      Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)) (standardGaussianPi d) := by
  have hi : ∀ l : Fin d, Integrable (fun x : ℝ => ↑x ^ p l *
      Complex.exp ((w l : ℂ) * Complex.I * x)) standardGaussianLine := by
    intro l
    have hz : (((w l : ℂ) * Complex.I).re) ∈ interior (integrableExpSet id standardGaussianLine) := by
      simp only [integrableExpSet_id_gaussianReal, interior_univ, mem_univ]
    exact integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet hz (p l)
  convert (Integrable.fintype_prod (μ := fun _ : Fin d => standardGaussianLine) hi) using 1
  funext Z
  exact gaussian_monomial_characteristic_product p w Z
def gaussianCrossExponent  (a b l : Fin d) : ℕ :=
  (if l = a then 1 else 0) + (if l = b then 1 else 0)
theorem gaussianCrossExponent_prod  (a b : Fin d) (Z : Covariate d) :
    (∏ l, (Z l : ℂ) ^ gaussianCrossExponent a b l) = (Z a : ℂ) * Z b := by
  have he (a : Fin d) : (∏ l, (Z l : ℂ) ^ (if l = a then 1 else 0)) = Z a := by
    have hh (l : Fin d) : (Z l : ℂ) ^ (if l = a then 1 else 0) =
        if l = a then (Z a : ℂ) else 1 := by
      split_ifs with hl
      · rw [hl, pow_one]
      · exact pow_zero _
    simp_rw [hh, Fintype.prod_ite_eq']
  simp only [gaussianCrossExponent, pow_add, Finset.prod_mul_distrib, he]
theorem standardGaussian_cross_complex_characteristic  (w a b) :
    (∫ Z, ((Z a ) * Z b) * Complex.exp ((gaussianPhase w Z ) * Complex.I)
      ∂standardGaussianPi d) =
      ((if a = b then 1 else 0) - w a  * w b) *
        Complex.exp ((-(∑ l, (w l) ^ 2) / 2 : ℝ) : ℂ) := by
  have h_standardGaussian_monomial_characteristic : (∫ Z, (∏ l, (Z l : ℂ) ^ (gaussianCrossExponent a b) l) * Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)
      ∂standardGaussianPi d) =
      (∏ l, gaussianFourierMomentFactor ((gaussianCrossExponent a b) l) (w l)) *
        Complex.exp ((-(∑ l, (w l) ^ 2) / 2 : ℝ) : ℂ) := by
    have h_gaussianCrossExponent_le_two (l : Fin d) : gaussianCrossExponent a b l ≤ 2 := by unfold gaussianCrossExponent; split_ifs <;> omega
    have hp  := h_gaussianCrossExponent_le_two
    simp_rw [gaussian_monomial_characteristic_product]
    rw [integral_fintype_prod_eq_prod (fun (l : Fin d) (x : ℝ) =>
      x ^ (gaussianCrossExponent a b) l * Complex.exp ((w l ) * Complex.I * x))]
    simp_rw [standardGaussian_line_fourier_moment _ (hp _) _, Finset.prod_mul_distrib]
    apply congrArg ((∏ l, gaussianFourierMomentFactor ((gaussianCrossExponent a b) l) (w l)) * ·)
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat,
      Complex.ofReal_sum, neg_div]
    rw [Finset.sum_neg_distrib, Finset.sum_div]
  have h_gaussianCrossExponent_factor_prod : (∏ l, gaussianFourierMomentFactor (gaussianCrossExponent a b l) (w l)) =
      (if a = b then 1 else 0) - w a  * w b := by
    by_cases hab : a = b
    · subst b
      have he (l : Fin d) : gaussianFourierMomentFactor (gaussianCrossExponent a a l) (w l) =
          if l = a then 1 - (w a : ℂ) ^ 2 else 1 := by
        by_cases hl : l = a <;> simp [gaussianCrossExponent, gaussianFourierMomentFactor, hl]
      simp_rw [he]
      rw [Fintype.prod_ite_eq']
      simp only [ite_true, pow_two]
    · have he (l : Fin d) : gaussianFourierMomentFactor (gaussianCrossExponent a b l) (w l) =
          (if l = a then (w a : ℂ) * Complex.I else 1) *
            (if l = b then (w b : ℂ) * Complex.I else 1) := by
        by_cases hla : l = a
        · subst l
          simp [gaussianCrossExponent, gaussianFourierMomentFactor, hab]
        · by_cases hlb : l = b
          · subst l
            simp [gaussianCrossExponent, gaussianFourierMomentFactor, Ne.symm hab]
          · simp [gaussianCrossExponent, gaussianFourierMomentFactor, hla, hlb]
      simp_rw [he, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
      rw [if_neg hab]
      calc
        _ = (w a : ℂ) * w b * Complex.I ^ 2 := by ring
        _ = _ := by rw [Complex.I_sq]; ring
  simpa only [gaussianCrossExponent_prod, h_gaussianCrossExponent_factor_prod] using (h_standardGaussian_monomial_characteristic)
theorem gaussian_cross_complex_characteristic_integrable  (w a b) :
    Integrable (fun Z => ((Z a : ℂ) * Z b) *
      Complex.exp ((gaussianPhase w Z : ℂ) * Complex.I)) (standardGaussianPi d) := by
  simpa only [gaussianCrossExponent_prod] using
    gaussian_monomial_characteristic_integrable (gaussianCrossExponent a b) w
def gaussianHermite  (a b : Fin d) (Z : Covariate d) : ℝ :=
  (if a = b then 1 else 0) - Z a * Z b
theorem standardGaussian_cross_integrable  (a b ) :
    Integrable (fun Z => Z a * Z b) (standardGaussianPi d) := by
  simpa [gaussianPhase, Complex.mul_re] using ((gaussian_cross_complex_characteristic_integrable (fun _ => 0) a b).re)
theorem standardGaussian_coordinate_square_integral  (a : Fin d) :
    (∫ Z : Covariate d, (Z a) ^ 2 ∂standardGaussianPi d) = 1 := by
  have h := standardGaussian_cross_complex_characteristic (fun _ => 0) a a
  simp [gaussianPhase] at h
  have he : (fun Z : Covariate d => (Z a : ℂ) * Z a) =
      (fun Z : Covariate d => (((Z a) ^ 2 : ℝ) : ℂ)) := by
    funext Z
    simp [pow_two]
  rw [he, integral_complex_ofReal] at h
  exact_mod_cast h
theorem gaussianHermite_integrable  (a b ) :
    Integrable (gaussianHermite a b) (standardGaussianPi d) :=
  (integrable_const _).sub (standardGaussian_cross_integrable a b)
def gaussianSpatialFrequency  (lam t : ℝ) (x y : Covariate d) : Covariate d :=
  fun l => Real.sqrt (2 * lam * t) * (y l - x l)
theorem standardGaussian_hermite_cos_integral_const  (w a b α β) :
    (∫ Z, gaussianHermite a b Z * α * β * Real.cos (gaussianPhase w Z)
      ∂standardGaussianPi d) =
      α * β * w a * w b * Real.exp (-(∑ l, (w l) ^ 2) / 2) := by
  have he : (fun Z => gaussianHermite a b Z * α * β * Real.cos (gaussianPhase w Z)) =
      (fun Z => α * β * (gaussianHermite a b Z * Real.cos (gaussianPhase w Z))) := by
    funext Z
    ring
  rw [he, integral_const_mul]
  unfold gaussianHermite
  have h_standardGaussian_hermite_cos_characteristic : (∫ Z, ((if a = b then 1 else 0) - Z a * Z b) *
      Real.cos (gaussianPhase w Z) ∂standardGaussianPi d) =
      w a * w b * Real.exp (-(∑ l, (w l) ^ 2) / 2) := by
    have h_gaussian_hermite_complex_characteristic_integrable : Integrable (fun Z => ((if a = b then 1 else 0) - Z a  * Z b) *
        Complex.exp ((gaussianPhase w Z ) * Complex.I)) (standardGaussianPi d) := by
      have hi := gaussian_monomial_characteristic_integrable (fun _ => 0) w
      simp only [pow_zero, Finset.prod_const_one, one_mul] at hi
      have h := (hi.const_mul (if a = b then 1 else 0)).sub
        (gaussian_cross_complex_characteristic_integrable w a b)
      convert h using 1
      funext Z
      exact sub_mul _ _ _
    have hi := h_gaussian_hermite_complex_characteristic_integrable
    have h_standardGaussian_hermite_complex_characteristic : (∫ Z, ((if a = b then 1 else 0) - Z a  * Z b) *
        Complex.exp ((gaussianPhase w Z ) * Complex.I) ∂standardGaussianPi d) =
        w a  * w b * Complex.exp ((-(∑ l, (w l) ^ 2) / 2 : ℝ) : ℂ) := by
      have hi := gaussian_monomial_characteristic_integrable (fun _ => 0) w
      simp only [pow_zero, Finset.prod_const_one, one_mul] at hi
      simp_rw [sub_mul]
      have h_standardGaussian_complex_characteristic : (∫ Z, Complex.exp ((gaussianPhase w Z ) * Complex.I) ∂standardGaussianPi d) =
          Complex.exp ((-(∑ l, (w l) ^ 2) / 2 : ℝ) : ℂ) := by
        have he : (fun Z => Complex.exp ((gaussianPhase w Z ) * Complex.I)) =
            (fun Z => ∏ l, Complex.exp ((w l ) * Z l * Complex.I)) := by
          funext Z
          simp only [gaussianPhase, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul,
            Complex.exp_sum]
        rw [he, integral_fintype_prod_eq_prod (fun (l : Fin d) (x : ℝ) =>
          Complex.exp ((w l : ℂ) * x * Complex.I))]
        have hc (l : Fin d) : (∫ x : ℝ, Complex.exp ((w l : ℂ) * x * Complex.I)
            ∂standardGaussianLine) = Complex.exp ((-(w l) ^ 2 / 2 : ℝ) : ℂ) := by
          rw [← charFun_apply_real, charFun_gaussianReal]
          simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one,
            one_mul, zero_sub, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow,
            Complex.ofReal_ofNat]
          congr 1
          ring
        simp_rw [hc]
        rw [← Complex.exp_sum]
        congr 1
        simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_ofNat,
          Complex.ofReal_sum, neg_div]
        rw [Finset.sum_neg_distrib, Finset.sum_div]
      rw [integral_sub (hi.const_mul _) (gaussian_cross_complex_characteristic_integrable w a b),
        integral_const_mul, h_standardGaussian_complex_characteristic,
        standardGaussian_cross_complex_characteristic]
      ring
    have h := congrArg Complex.re h_standardGaussian_hermite_complex_characteristic
    have hre := integral_re hi
    change (∫ Z, (((if a = b then 1 else 0) - Z a  * Z b) *
      Complex.exp ((gaussianPhase w Z ) * Complex.I)).re ∂standardGaussianPi d) =
        (∫ Z, ((if a = b then 1 else 0) - Z a  * Z b) *
          Complex.exp ((gaussianPhase w Z ) * Complex.I) ∂standardGaussianPi d).re at hre
    rw [← hre] at h
    simpa only [Complex.sub_re, Complex.mul_re, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, add_zero, zero_add,
      mul_zero, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_re,
      apply_ite Complex.re, Complex.one_re, Complex.zero_re, apply_ite Complex.im,
      Complex.one_im, Complex.zero_im, ite_self] using h
  rw [h_standardGaussian_hermite_cos_characteristic]
  ring
end
section
variable {n : ℕ} {b : ℝ}
theorem gamma_monomial_integrable  (hb : 0 < b) (r ) :
    IntegrableOn (fun v => v ^ r * Real.exp (-(b * v))) (Ici 0) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := r) (p := 1)
    (b := b) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg r)) (by norm_num) hb
  simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using h
theorem gamma_monomial_integral  (hb : 0 < b) (r : ℕ) :
    (∫ v : ℝ in Ici 0, v ^ r * Real.exp (-(b * v))) =
      r.factorial / b ^ (r + 1) := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := r + 1)
    (r := b) (by positivity) hb
  simp only [add_sub_cancel_right, Real.rpow_natCast, Real.Gamma_nat_eq_factorial] at h
  rw [h]
  have he : ↑r + 1 = ((r + 1 : ℕ) : ℝ) := by norm_num
  rw [he, Real.rpow_natCast, div_pow, one_pow]
  field_simp
theorem gamma_polynomial_tail_integral  (hb : 0 < b) (A ) (m : ℕ) :
    (∫ u : ℝ in Ici A, u ^ m * Real.exp (-(b * u)) / m.factorial) =
      Real.exp (-(b * A)) *
        ∑ l ∈ Finset.range (m + 1), A ^ l / (l.factorial * b ^ (m + 1 - l)) := by
  have h_integral_Ici_translate (f : ℝ → ℝ) : (∫ v : ℝ in Ici 0, f (A + v)) = ∫ u : ℝ in Ici A, f u := by
    have hp := (measurePreserving_add_left (volume : Measure ℝ) A).restrict_preimage
      (s := Ici A) measurableSet_Ici
    have hs : (fun v => A + v) ⁻¹' Ici A = Ici 0 := by
      ext v
      simp only [mem_preimage, mem_Ici]
      constructor <;> intro h <;> linarith
    rw [hs] at hp
    exact hp.integral_comp (MeasurableEquiv.addLeft A).measurableEmbedding f
  rw [← h_integral_Ici_translate]
  have he : (fun v => (A + v) ^ m * Real.exp (-(b * (A + v))) / m.factorial) =
      fun v => (Real.exp (-(b * A)) / m.factorial) *
        ∑ l ∈ Finset.range (m + 1),
          (A ^ l * (m.choose l )) * (v ^ (m - l) * Real.exp (-(b * v))) := by
    funext v
    rw [show -(b * (A + v)) = -(b * A) + -(b * v) by ring, Real.exp_add,
      add_pow, Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [he, integral_const_mul, integral_finsetSum _ (fun l _ =>
    (gamma_monomial_integrable hb (m - l)).const_mul _)]
  simp_rw [integral_const_mul, gamma_monomial_integral hb]
  rw [div_mul_eq_mul_div, div_eq_mul_inv, mul_assoc]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l hl
  have hlm  := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
  have : m.factorial ≠ 0 := by positivity
  have : l.factorial ≠ 0 := by positivity
  have : ((m - l).factorial : ℝ) ≠ 0 := by positivity
  have  := ne_of_gt hb
  have hchoose := Nat.cast_choose ℝ hlm
  rw [hchoose]
  have hn : m + 1 - l = m - l + 1 := by omega
  rw [hn]
  field_simp
theorem gamma_polynomial_tail_integrable  (hb : 0 < b) (A ) (m : ℕ) :
    IntegrableOn (fun u => u ^ m * Real.exp (-(b * u)) / m.factorial)
      (Ici A) := by
  have hp := (measurePreserving_add_left (volume : Measure ℝ) A).restrict_preimage
    (s := Ici A) measurableSet_Ici
  have hs : (fun v => A + v) ⁻¹' Ici A = Ici 0 := by
    ext v
    simp only [mem_preimage, mem_Ici]
    constructor <;> intro h <;> linarith
  rw [hs] at hp
  apply (hp.integrable_comp_emb (MeasurableEquiv.addLeft A).measurableEmbedding).mp
  have h_gamma_translated_monomial_integrable : IntegrableOn (fun v => (A + v) ^ m * Real.exp (-b * v)) (Ici 0) := by
    have he : (fun v => (A + v) ^ m * Real.exp (-b * v)) =
        fun v => ∑ l ∈ Finset.range (m + 1),
          (A ^ l * m.choose l ) * (v ^ (m - l) * Real.exp (-(b * v))) := by
      funext v
      rw [add_pow, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    exact integrable_finsetSum _ fun l _ => (gamma_monomial_integrable hb (m - l)).const_mul _
  have h := h_gamma_translated_monomial_integrable.const_mul
    (Real.exp (-b * A) / m.factorial)
  convert h using 1
  funext v
  simp only [Function.comp_apply]
  rw [show -(b * (A + v)) = -(b * A) + -(b * v) by ring, Real.exp_add]
  ring
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def exponentialOrthantMeasure (ι ) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => volume.restrict (Ici 0))
instance exponentialOrthantMeasure_sigmaFinite : SigmaFinite (exponentialOrthantMeasure ι) := by
  unfold exponentialOrthantMeasure
  infer_instance
def orthantExponential (b : ℝ) (s : ι → ℝ) : ℝ := Real.exp (-(b * ∑ j, s j))
def orthantHeadTail (b A : ℝ) (s : ι → ℝ) : ℝ :=
  Real.exp (-(b * max A (∑ j, s j))) / b
def orthantCoordinateTail (b A : ℝ) (j : ι) (s : ι → ℝ) : ℝ :=
  ∏ l, if l = j then (Ioi A).indicator (fun v => Real.exp (-(b * v))) (s l)
    else Real.exp (-(b * s l))
theorem exponential_orthant_measure_eq_restrict :
    exponentialOrthantMeasure ι = volume.restrict (Ici (0 : ι → ℝ)) := by
  have hs : Ici (0 : ι → ℝ) = Set.univ.pi (fun _ => Ici 0) := by
    ext s
    simp only [mem_Ici, mem_pi, mem_univ, forall_true_left]
    rfl
  rw [hs]
  exact (Measure.restrict_pi_pi (μ := fun _ => (volume : Measure ℝ)) _).symm
theorem orthant_exponential_product (b : ℝ) (s : ι → ℝ) :
    orthantExponential b s = ∏ j, Real.exp (-(b * s j)) := by
  unfold orthantExponential
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.sum_neg_distrib]
theorem scalar_exponential_integrable  (hb : 0 < b) :
    IntegrableOn (fun v => Real.exp (-(b * v))) (Ici 0) := by
  simpa only [pow_zero, one_mul] using gamma_monomial_integrable hb 0
theorem orthant_exponential_integrable  (hb : 0 < b) :
    Integrable (orthantExponential b : (ι → ℝ) → ℝ) (exponentialOrthantMeasure ι) := by
  change Integrable (fun s : ι → ℝ => orthantExponential b s) (exponentialOrthantMeasure ι)
  simp_rw [orthant_exponential_product]
  exact Integrable.fintype_prod (𝕜 := ℝ)
    (f := fun (_ : ι) v => Real.exp (-(b * v)))
    (μ := fun _ => volume.restrict (Ici 0))
    (fun _ => scalar_exponential_integrable hb)
theorem orthant_coordinate_tail_nonnegative (b A : ℝ) (j : ι) (s : ι → ℝ) :
    0 ≤ orthantCoordinateTail b A j s := by
  apply Finset.prod_nonneg
  intro l _
  split_ifs
  · exact Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _
  · exact Real.exp_nonneg _
theorem orthant_cube_indicator_integrable (A C : ℝ) :
    Integrable ((Icc (0 : ι → ℝ) (fun _ => A)).indicator (fun _ => C))
      (exponentialOrthantMeasure ι) := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  rw [IntegrableOn, exponential_orthant_measure_eq_restrict,
    Measure.restrict_restrict_of_subset (fun _ hs => hs.1)]
  exact integrableOn_const (isCompact_Icc.measure_lt_top.ne)
theorem orthant_cube_indicator_integral  (hA : 0 ≤ A) (C ) :
    (∫ s : ι → ℝ, (Icc (0 : ι → ℝ) (fun _ => A)).indicator (fun _ => C) s
      ∂exponentialOrthantMeasure ι) = A ^ Fintype.card ι * C := by
  rw [integral_indicator measurableSet_Icc, exponential_orthant_measure_eq_restrict,
    Measure.restrict_restrict_of_subset (fun _ hs => hs.1), integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
  have hvol := Real.volume_Icc_pi_toReal (a := (0 : ι → ℝ)) (b := fun _ => A)
    (fun _ => hA)
  rw [hvol]
  simp only [Pi.zero_apply, sub_zero, Finset.prod_const, Finset.card_univ]
def orthantSumTail (b A : ℝ) (z : ℝ × (ι → ℝ)) : ℝ :=
  if A ≤ z.1 + ∑ j, z.2 j then Real.exp (-(b * (z.1 + ∑ j, z.2 j))) else 0
theorem orthant_sum_tail_integrable  (hb : 0 < b) (A ) :
    Integrable (orthantSumTail b A : (ℝ × (ι → ℝ)) → ℝ)
      ((volume.restrict (Ici ↑0)).prod (exponentialOrthantMeasure ι)) := by
  have hbase := (scalar_exponential_integrable hb).mul_prod (orthant_exponential_integrable (ι := ι) hb)
  have he : (fun z : ℝ × (ι → ℝ) => Real.exp (-(b * z.1)) * orthantExponential b z.2) =
      fun z => Real.exp (-(b * (z.1 + ∑ j, z.2 j))) := by
    funext z
    unfold orthantExponential
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hbase
  have hmeas : MeasurableSet {z : ℝ × (ι → ℝ) | A ≤ z.1 + ∑ j, z.2 j} :=
    measurableSet_le measurable_const
      (measurable_fst.add (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).comp measurable_snd))
  convert hbase.indicator hmeas using 1
  funext z
  simp only [orthantSumTail, Set.indicator, mem_setOf_eq]
theorem orthant_sum_tail_integral_uniform  (hb : (1 / 2 : ℝ) ≤ b)
    (hA : 0 ≤ A) :
    (∫ z : ℝ × (ι → ℝ), orthantSumTail b A z
      ∂((volume.restrict (Ici 0)).prod (exponentialOrthantMeasure ι))) ≤
      8 ^ (Fintype.card ι + 1) * Real.exp (-(b * A)) * (1 + A) ^ Fintype.card ι := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hinv : 1 / b ≤ 2 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hb
  have hpow : (1 / b) ^ (Fintype.card ι + 1) ≤ 2 ^ (Fintype.card ι + 1) :=
    pow_le_pow_left₀ (by positivity) hinv _
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : 1 ≤ Fintype.card ι + 1)
  have hAone : 1 ≤ (1 + A) ^ Fintype.card ι := one_le_pow₀ (by linarith)
  have : A ^ Fintype.card ι / b ≤
      2 ^ (Fintype.card ι + 1) * (1 + A) ^ Fintype.card ι := by
    have h := mul_le_mul (pow_le_pow_left₀ hA (by linarith) _) (hinv.trans (by simpa using h)) (by positivity : 0 ≤ 1 / b)
      (by positivity : 0 ≤ (1 + A) ^ Fintype.card ι)
    convert h using 1 <;> ring
  have : (Fintype.card ι ) / b ^ (Fintype.card ι + 1) ≤
      (Fintype.card ι ) * 2 ^ (Fintype.card ι + 1) * (1 + A) ^ Fintype.card ι := by
    have h := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (Fintype.card ι) : ↑0 ≤ _)
    have hh := mul_le_mul_of_nonneg_left hAone
      (by positivity : 0 ≤ (Fintype.card ι : ℝ) * 2 ^ (Fintype.card ι + 1))
    rw [div_pow, one_pow] at h
    calc
      _ = (Fintype.card ι ) * (1 / b ^ (Fintype.card ι + 1)) := by ring
      _ ≤ _ := h
      _ ≤ _ := by simpa using hh
  have hconst : ((Fintype.card ι ) + 1) * 2 ^ (Fintype.card ι + 1) ≤
      (8 : ℝ) ^ (Fintype.card ι + 1) := by
    have h_nat_add_two_le_four_pow (m : ℕ) : ↑m + 2 ≤ (4 : ℝ) ^ (m + 1) := by
      induction m with
      | zero => norm_num
      | succ m ih =>
        rw [Nat.cast_succ, show m + 1 + 1 = (m + 1) + 1 by omega, pow_succ]
        nlinarith
    have h := mul_le_mul_of_nonneg_right (h_nat_add_two_le_four_pow (Fintype.card ι))
      (by positivity : 0 ≤ (2 : ℝ) ^ (Fintype.card ι + 1))
    rw [← mul_pow] at h
    norm_num only at h
    nlinarith
  have hsum : A ^ Fintype.card ι / b + (Fintype.card ι : ℝ) / b ^ (Fintype.card ι + 1) ≤
      8 ^ (Fintype.card ι + 1) * (1 + A) ^ Fintype.card ι := by
    have h := mul_le_mul_of_nonneg_right hconst (by positivity : 0 ≤ (1 + A) ^ Fintype.card ι)
    nlinarith
  have h := mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg (-(b * A)))
  have h_orthant_sum_tail_integral_le : (∫ z : ℝ × (ι → ℝ), orthantSumTail b A z
      ∂((volume.restrict (Ici 0)).prod (exponentialOrthantMeasure ι))) ≤
      Real.exp (-(b * A)) *
        (A ^ Fintype.card ι / b + (Fintype.card ι : ℝ) / b ^ (Fintype.card ι + 1)) := by
    have h_scalar_exponential_tail_integral (A) : (∫ v : ℝ in Ici A, Real.exp (-(b * v))) = Real.exp (-(b * A)) / b := by
      simpa [div_eq_mul_inv] using gamma_polynomial_tail_integral hbpos A 0
    have h_orthant_coordinate_tail_integrable (j) : Integrable (orthantCoordinateTail b A j) (exponentialOrthantMeasure ι) := by
      exact Integrable.fintype_prod (𝕜 := ℝ)
        (f := fun (l : ι) v => if l = j then
          (Ioi A).indicator (fun v => Real.exp (-(b * v))) v else Real.exp (-(b * v)))
        (μ := fun _ => volume.restrict (Ici 0)) (fun l => by
          split_ifs
          · exact ((scalar_exponential_integrable hbpos).indicator measurableSet_Ioi)
          · exact scalar_exponential_integrable hbpos)
    have h_orthant_head_tail_le_exponential (A : ℝ) (s : ι → ℝ) : orthantHeadTail b A s ≤ orthantExponential b s / b := by
      apply div_le_div_of_nonneg_right _ hbpos.le
      apply Real.exp_le_exp.mpr
      have := le_max_right A (∑ j, s j)
      nlinarith
    have h_orthant_sum_tail_integral_eq (A : ℝ) : (∫ z : ℝ × (ι → ℝ), orthantSumTail b A z
        ∂((volume.restrict (Ici ↑0)).prod (exponentialOrthantMeasure ι))) =
        ∫ s : ι → ℝ, orthantHeadTail b A s ∂exponentialOrthantMeasure ι := by
      rw [integral_prod_symm _ (orthant_sum_tail_integrable hbpos A)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => by
        have he : (fun v : ℝ => orthantSumTail b A (v, s)) =
            fun v => (Ici (A - ∑ j, s j)).indicator
              (fun v : ℝ => Real.exp (-(b * (v + ∑ j, s j)))) v := by
          funext v
          have hh : A ≤ v + ∑ j, s j ↔ A - ∑ j, s j ≤ v := by constructor <;> intro h <;> linarith
          simp only [orthantSumTail, Set.indicator, mem_Ici, hh]
        dsimp only
        have h_orthant_head_tail_scalar_integral (A : ℝ) (S : ℝ) : (∫ v : ℝ in Ici 0,
          (Ici (A - S)).indicator (fun v : ℝ => Real.exp (-(b * (v + S)))) v) =
          Real.exp (-(b * max A S)) / b := by
          rw [integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
            Set.Ici_inter_Ici]
          have he : (fun v : ℝ => Real.exp (-(b * (v + S)))) =
              fun v => Real.exp (-(b * S)) * Real.exp (-(b * v)) := by
            funext v
            rw [← Real.exp_add]
            congr 1
            ring
          rw [he, integral_const_mul, h_scalar_exponential_tail_integral, div_eq_mul_inv, ← mul_assoc, ← Real.exp_add]
          have hmax : S + max (A - S) 0 = max A S := by
            by_cases h : S ≤ A
            · rw [max_eq_left (by linarith), max_eq_left h]
              ring
            · rw [max_eq_right (by linarith), max_eq_right (le_of_not_ge h)]
              ring
          rw [show -(b * S) + -(b * max (A - S) 0) = -(b * (S + max (A - S) 0)) by ring,
            hmax]
          rfl
        rw [he, h_orthant_head_tail_scalar_integral]
        rfl
    rw [h_orthant_sum_tail_integral_eq]
    let cube := Icc (0 : ι → ℝ) (fun _ => A)
    let G := fun s : ι → ℝ => cube.indicator (fun _ => Real.exp (-(b * A)) / b) s +
      (1 / b) * ∑ j, orthantCoordinateTail b A j s
    have hG : Integrable G (exponentialOrthantMeasure ι) :=
      (orthant_cube_indicator_integrable A _).add
        ((integrable_finsetSum _ fun j _ => h_orthant_coordinate_tail_integrable j).const_mul _)
    have hdom : (orthantHeadTail b A : (ι → ℝ) → ℝ) ≤ᵐ[exponentialOrthantMeasure ι] G := by
      filter_upwards [(by rw [exponential_orthant_measure_eq_restrict]; exact ae_restrict_mem measurableSet_Ici)] with s hs
      have hsum : 0 ≤ ∑ j, orthantCoordinateTail b A j s :=
        Finset.sum_nonneg fun j _ => orthant_coordinate_tail_nonnegative b A j s
      by_cases hcube : s ∈ cube
      · simp only [G, Set.indicator_of_mem hcube]
        have h_orthant_head_tail_le_constant : orthantHeadTail b A s ≤ Real.exp (-(b * A)) / b := by
          apply div_le_div_of_nonneg_right _ hbpos.le
          apply Real.exp_le_exp.mpr
          have h := le_max_left A (∑ j, s j)
          nlinarith
        have h := h_orthant_head_tail_le_constant
        nlinarith [mul_nonneg (by positivity : 0 ≤ 1 / b) hsum]
      · have hex : ∃ j, A < s j := by
          by_contra h
          apply hcube
          refine ⟨hs, ?_⟩
          intro j
          exact le_of_not_gt (fun hj => h ⟨j, hj⟩)
        obtain ⟨j, hj⟩ := hex
        have hterm : orthantCoordinateTail b A j s ≤ ∑ l, orthantCoordinateTail b A l s :=
          Finset.single_le_sum (fun l _ => orthant_coordinate_tail_nonnegative b A l s)
            (Finset.mem_univ j)
        have h_orthant_coordinate_tail_eq_exponential : orthantCoordinateTail b A j s = orthantExponential b s := by
          rw [orthant_exponential_product]
          apply Finset.prod_congr rfl
          intro l _
          split_ifs with h
          · subst l
            exact Set.indicator_of_mem hj _
          · rfl
        rw [h_orthant_coordinate_tail_eq_exponential] at hterm
        simp only [G, Set.indicator_of_notMem hcube, zero_add]
        have h := h_orthant_head_tail_le_exponential A s
        have hm := mul_le_mul_of_nonneg_left hterm (by positivity : 0 ≤ 1 / b)
        calc
          _ ≤ orthantExponential b s / b := h
          _ ≤ _ := by convert hm using 1 <;> ring
    have h_orthant_head_tail_integrable : Integrable (orthantHeadTail b A : (ι → ℝ) → ℝ) (exponentialOrthantMeasure ι) := by
      have hcont : Continuous (orthantHeadTail b A : (ι → ℝ) → ℝ) :=
        (Real.continuous_exp.comp (continuous_const.mul
          (continuous_const.max (continuous_finsetSum _ fun j _ => continuous_apply j))).neg).div_const b
      exact ((orthant_exponential_integrable hbpos).div_const b).mono' hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun s => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by unfold orthantHeadTail; positivity)]
          exact h_orthant_head_tail_le_exponential A s)
    have h := integral_mono_ae h_orthant_head_tail_integrable hG hdom
    dsimp [G] at h
    have h_orthant_coordinate_tail_integral (j : ι) : (∫ s : ι → ℝ, orthantCoordinateTail b A j s ∂exponentialOrthantMeasure ι) =
        Real.exp (-(b * A)) / b ^ Fintype.card ι := by
      unfold orthantCoordinateTail exponentialOrthantMeasure
      rw [integral_fintype_prod_eq_prod (fun (l : ι) (v : ℝ) => if l = j then
        (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) v else Real.exp (-(b * v)))]
      have he : (fun l : ι => ∫ v : ℝ in Ici 0,
          if l = j then (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) v
          else Real.exp (-(b * v))) =
          fun l => if l = j then Real.exp (-(b * A)) / b else 1 / b := by
        funext l
        split_ifs
        have h_scalar_exponential_indicator_integral : (∫ v : ℝ in Ici 0, (Ioi A).indicator (fun v : ℝ => Real.exp (-(b * v))) v) =
          Real.exp (-(b * A)) / b := by
          rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi]
          have hs : Ioi A ∩ Ici ↑0 = Ioi A := by
            apply Set.inter_eq_left.mpr
            intro v hv
            exact le_of_lt (lt_of_le_of_lt hA hv)
          rw [hs, ← integral_Ici_eq_integral_Ioi, h_scalar_exponential_tail_integral]
        · exact h_scalar_exponential_indicator_integral
        · simpa using h_scalar_exponential_tail_integral ↑0
      rw [he, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
      simp only [ite_true]
      have hp : (∏ l ∈ (Finset.univ : Finset ι).erase j,
          if l = j then Real.exp (-(b * A)) / b else 1 / b) =
          (1 / b) ^ (Fintype.card ι - 1) := by
        calc
          _ = ∏ _l ∈ (Finset.univ : Finset ι).erase j, (1 / b : ℝ) := by
            apply Finset.prod_congr rfl
            intro l hl
            exact ite_eq_right (Finset.mem_erase.mp hl).1
          _ = _ := by rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ j)]; rfl
      rw [hp]
      have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨j⟩
      have hn : Fintype.card ι = (Fintype.card ι - 1) + 1 := by omega
      have hpow : b ^ Fintype.card ι = b ^ (Fintype.card ι - 1) * b := by
        conv_lhs => rw [hn]
        rw [pow_succ]
      rw [hpow, div_pow, one_pow]
      field_simp
    rw [integral_add (orthant_cube_indicator_integrable A _)
      ((integrable_finsetSum _ fun j _ => h_orthant_coordinate_tail_integrable j).const_mul _),
      orthant_cube_indicator_integral hA, integral_const_mul,
      integral_finsetSum _ (fun j _ => h_orthant_coordinate_tail_integrable j)] at h
    simp_rw [h_orthant_coordinate_tail_integral] at h
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    convert h using 1 <;> rw [pow_succ] <;> ring
  calc
    _ ≤ _ := h_orthant_sum_tail_integral_le
    _ ≤ _ := by convert h using 1 <;> ring
def finiteOrthantTail  (b A : ℝ) (s : Fin q → ℝ) : ℝ :=
  if A ≤ ∑ j, s j then Real.exp (-(b * ∑ j, s j)) else 0
end
section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
def exponentialScaleMap (s : ι → ℝ) : ι → ℝ := fun j => Real.exp (s j) - 1
def exponentialScaleDerivative (s : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun j => Real.exp (s j) • ContinuousLinearMap.proj j)
theorem exponential_scale_hasFDerivAt (s : ι → ℝ) :
    HasFDerivAt exponentialScaleMap (exponentialScaleDerivative s) s := by
  apply hasFDerivAt_pi.mpr
  intro j
  have h : HasFDerivAt (fun x => Real.exp (x j))
      (Real.exp (s j) • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) j)) s := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (s j)).comp_hasFDerivAt s (hasFDerivAt_apply j s)
  exact h.sub_const 1
theorem exponential_scale_derivative_det (s : ι → ℝ) :
    (exponentialScaleDerivative s).det = ∏ j, Real.exp (s j) := by
  have he : (exponentialScaleDerivative s).toLinearMap =
      LinearMap.pi (fun j => ((Real.exp (s j)) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)).comp (LinearMap.proj j)) := by
    ext v j
    rfl
  change (exponentialScaleDerivative s).toLinearMap.det = _
  rw [he, LinearMap.det_pi]
  simp only [LinearMap.det_smul, Module.finrank_self, pow_one, LinearMap.det_id, mul_one]
theorem exponential_scale_injective : Function.Injective (exponentialScaleMap : (ι → ℝ) → (ι → ℝ)) := by
  intro s t h
  funext j
  apply Real.exp_injective
  have hj := congrFun h j
  change Real.exp (s j) - 1 = Real.exp (t j) - 1 at hj
  linarith
theorem exponential_scale_image_orthant :
    exponentialScaleMap '' Ici (0 : ι → ℝ) = Ici (0 : ι → ℝ) := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    intro j
    change 0 ≤ Real.exp (s j) - 1
    linarith [Real.one_le_exp_iff.mpr (hs j)]
  · intro ht
    refine ⟨fun j => Real.log (1 + t j), ?_, ?_⟩
    · intro j
      have : 0 ≤ t j := ht j
      exact Real.log_nonneg (by linarith)
    · funext j
      have : 0 ≤ t j := ht j
      change Real.exp (Real.log (1 + t j)) - 1 = t j
      rw [Real.exp_log (by linarith)]
      ring
theorem integral_exponential_scale_change (f : (ι → ℝ) → ℝ) :
    (∫ t : ι → ℝ in Ici 0, f t) =
      ∫ s : ι → ℝ in Ici 0, (∏ j, Real.exp (s j)) * f (exponentialScaleMap s) := by
  have h := integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure (ι → ℝ))
    (s := Ici 0) measurableSet_Ici
    (fun s _ => (exponential_scale_hasFDerivAt s).hasFDerivWithinAt)
    exponential_scale_injective.injOn f
  rw [exponential_scale_image_orthant] at h
  have hdet : ∀ s : ι → ℝ, |(exponentialScaleDerivative s).det| = ∏ j, Real.exp (s j) := by
    intro s
    rw [exponential_scale_derivative_det, abs_of_nonneg (Finset.prod_nonneg (fun j _ => Real.exp_nonneg _))]
  simp_rw [hdet, smul_eq_mul] at h
  exact h
theorem integrableOn_exponential_scale_change_iff (f : (ι → ℝ) → ℝ) :
    IntegrableOn f (Ici 0) ↔
      IntegrableOn (fun s : ι → ℝ => (∏ j, Real.exp (s j)) * f (exponentialScaleMap s)) (Ici 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul (volume : Measure (ι → ℝ))
    (s := Ici 0) measurableSet_Ici
    (fun s _ => (exponential_scale_hasFDerivAt s).hasFDerivWithinAt)
    exponential_scale_injective.injOn f
  rw [exponential_scale_image_orthant] at h
  have hdet : ∀ s : ι → ℝ, |(exponentialScaleDerivative s).det| = ∏ j, Real.exp (s j) := by
    intro s
    rw [exponential_scale_derivative_det, abs_of_nonneg (Finset.prod_nonneg (fun j _ => Real.exp_nonneg _))]
  simp_rw [hdet, smul_eq_mul] at h
  exact h
def logScaleTail (b A : ℝ) (t : ι → ℝ) : ℝ :=
  if A ≤ ∑ j, Real.log (1 + t j) then ∏ j, (1 + t j) ^ (-b - 1 ) else 0
theorem log_scale_tail_change_pointwise (b A : ℝ) (s : ι → ℝ) :
    (∏ j, Real.exp (s j)) * logScaleTail b A (exponentialScaleMap s) =
      if A ≤ ∑ j, s j then Real.exp (-(b * ∑ j, s j)) else 0 := by
  have he : ∀ j, 1 + exponentialScaleMap s j = Real.exp (s j) := by
    intro j
    unfold exponentialScaleMap
    ring
  unfold logScaleTail
  simp_rw [he, Real.log_exp]
  split_ifs
  · rw [← Finset.prod_mul_distrib]
    have hp : ∀ j, Real.exp (s j) * Real.exp (s j) ^ (-b - 1 ) =
        Real.exp (-(b * s j)) := by
      intro j
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    simp_rw [hp]
    rw [← Real.exp_sum]
    congr 1
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  · exact mul_zero _
end
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
theorem log_scale_tail_reindex (e : κ ≃ ι) (b A s) :
    logScaleTail b A ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) s) = logScaleTail b A s := by
  have hs := e.sum_comp (fun j => Real.log (1 + ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) s) j))
  have hp := e.prod_comp (fun j => (1 + ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) s) j) ^ (-b - 1 ))
  simp only [MeasurableEquiv.piCongrLeft_apply_apply] at hs hp
  unfold logScaleTail
  rw [← hs, ← hp]
theorem log_scale_tail_integral_reindex (e : κ ≃ ι) (b A ) :
    (∫ t : ι → ℝ in Ici 0, logScaleTail b A t) =
      ∫ s : κ → ℝ in Ici 0, logScaleTail b A s := by
  rw [← exponential_orthant_measure_eq_restrict, ← exponential_orthant_measure_eq_restrict]
  unfold exponentialOrthantMeasure
  rw [← (measurePreserving_piCongrLeft (fun _ => volume.restrict (Ici 0)) e).integral_comp']
  simp_rw [log_scale_tail_reindex]
theorem log_scale_tail_integrable_of_card  (hcard : Fintype.card ι = m + 1)
     (hb : 0 < b) (A ) :
    IntegrableOn (logScaleTail b A : (ι → ℝ) → ℝ) (Ici 0) := by
  let e : Fin (m + 1) ≃ ι := (Fintype.equivFinOfCardEq hcard).symm
  have hp := measurePreserving_piCongrLeft (fun _ : ι => volume.restrict (Ici (0 : ℝ))) e
  rw [IntegrableOn, ← exponential_orthant_measure_eq_restrict]
  apply (hp.integrable_comp_emb (MeasurableEquiv.piCongrLeft (fun _ : ι => ℝ) e).measurableEmbedding).mp
  have he : (logScaleTail b A) ∘ (MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) =
      (logScaleTail b A : (Fin (m + 1) → ℝ) → ℝ) := by
    funext s
    exact log_scale_tail_reindex e b A s
  rw [he]
  have h_finite_log_scale_tail_integrable : IntegrableOn (logScaleTail b A : (Fin (m + 1) → ℝ) → ℝ) (Ici 0) := by
    apply (integrableOn_exponential_scale_change_iff _).mpr
    have h_finite_orthant_tail_integrable : Integrable (finiteOrthantTail b A : (Fin (m + 1) → ℝ) → ℝ)
        (exponentialOrthantMeasure (Fin (m + 1))) := by
      have hp := (measurePreserving_piFinSuccAbove
        (fun _ : Fin (m + 1) => volume.restrict (Ici (0 : ℝ))) 0).symm
      apply (hp.integrable_comp_emb (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm.measurableEmbedding).mp
      convert orthant_sum_tail_integrable (ι := Fin m) hb A using 1
      · funext z
        simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          finiteOrthantTail, orthantSumTail, Fin.sum_univ_succ, Fin.insertNth_zero,
          Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      · rfl
    have h := h_finite_orthant_tail_integrable
    rw [exponential_orthant_measure_eq_restrict] at h
    have he : (fun s : Fin (m + 1) → ℝ => (∏ j, Real.exp (s j)) *
        logScaleTail b A (exponentialScaleMap s)) = finiteOrthantTail b A := by
      funext s
      exact log_scale_tail_change_pointwise b A s
    rw [he]
    exact h
  have h := h_finite_log_scale_tail_integrable
  rw [IntegrableOn, ← exponential_orthant_measure_eq_restrict] at h
  exact h
def strictLogScaleTail (b A : ℝ) (t : ι → ℝ) : ℝ :=
  ({t : ι → ℝ | A < ∑ j, Real.log (1 + t j)}).indicator (logScaleTail b A) t
theorem strict_log_scale_tail_integrable_of_card  (hcard : Fintype.card ι = m + 1)
     (hb : 0 < b) (A ) :
    IntegrableOn (strictLogScaleTail b A : (ι → ℝ) → ℝ) (Ici 0) := by
  exact (log_scale_tail_integrable_of_card hcard hb A).indicator
    (measurableSet_lt measurable_const (Finset.measurable_sum _ fun j _ =>
      Real.measurable_log.comp (measurable_const.add (measurable_pi_apply j))))
theorem strict_log_scale_tail_integral_le  (hcard : Fintype.card ι = m + 1)
    {b A : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hA : 0 ≤ A) :
    (∫ t : ι → ℝ in Ici 0, strictLogScaleTail b A t) ≤
      8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
  have hbpos : 0 < b := lt_of_lt_of_le (by norm_num) hb
  have hnonneg : ∀ᵐ t : ι → ℝ ∂volume.restrict (Ici 0), 0 ≤ logScaleTail b A t := by
    filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Ici (0 : ι → ℝ)))] with t ht
    unfold logScaleTail
    split_ifs
    · apply Finset.prod_nonneg
      intro j _
      have : 0 ≤ t j := ht j
      exact Real.rpow_nonneg (by linarith) _
    · exact le_refl _
  have h_finite_log_scale_tail_integral_uniform : (∫ t : Fin (m + 1) → ℝ in Ici 0, logScaleTail b A t) ≤
      8 ^ (m + 1) * Real.exp (-(b * A)) * (1 + A) ^ m := by
    have h_finite_log_scale_tail_integral {q} : (∫ t : Fin q → ℝ in Ici 0, logScaleTail b A t) =
        ∫ s : Fin q → ℝ, finiteOrthantTail b A s ∂exponentialOrthantMeasure (Fin q) := by
      rw [integral_exponential_scale_change, exponential_orthant_measure_eq_restrict]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun s => log_scale_tail_change_pointwise b A s
    rw [h_finite_log_scale_tail_integral]
    have h_finite_orthant_tail_split_integral : (∫ s : Fin (m + 1) → ℝ, finiteOrthantTail b A s
        ∂exponentialOrthantMeasure (Fin (m + 1))) =
        ∫ z : ℝ × (Fin m → ℝ), orthantSumTail b A z
        ∂((volume.restrict (Ici 0)).prod (exponentialOrthantMeasure (Fin m))) := by
      unfold exponentialOrthantMeasure
      rw [← ((measurePreserving_piFinSuccAbove
        (fun _ => volume.restrict (Ici 0)) 0).symm).integral_comp']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          finiteOrthantTail, orthantSumTail, Fin.sum_univ_succ, Fin.insertNth_zero,
          Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    rw [h_finite_orthant_tail_split_integral]
    simpa using orthant_sum_tail_integral_uniform (ι := Fin m) hb hA
  calc
    _ ≤ ∫ t : ι → ℝ in Ici 0, logScaleTail b A t :=
      integral_mono_ae (strict_log_scale_tail_integrable_of_card hcard hbpos A)
        (log_scale_tail_integrable_of_card hcard hbpos A) (by
          filter_upwards [hnonneg] with t ht
          unfold strictLogScaleTail
          by_cases hh : t ∈ {t : ι → ℝ | A < ∑ j, Real.log (1 + t j)}
          · simp only [Set.indicator_of_mem hh, le_refl]
          · simp only [Set.indicator_of_notMem hh]
            exact ht)
    _ ≤ _ := (by rw [log_scale_tail_integral_reindex (Fintype.equivFinOfCardEq hcard).symm]; exact h_finite_log_scale_tail_integral_uniform)
theorem spatial_scale_index_card  (i : Fin n) : Fintype.card (SpatialScaleIndex i) = n - 1 := by
  simp [SpatialScaleIndex]
theorem spatial_scale_complement_power_integrable  (hn : 2 ≤ n) (i : Fin n)
     (hb : 0 < b) (T : ℝ) :
    IntegrableOn (fun t : SpatialScaleVector i => ∏ j, (1 + t j) ^ (-b - 1 : ℝ))
      (Ici 0 \ spatialScaleDomain i T) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = n - 2 + 1 := by
    rw [spatial_scale_index_card]
    omega
  have h := (strict_log_scale_tail_integrable_of_card hcard hb (2 * Real.log T)).mono_set
    (Set.diff_subset : Ici (0 : SpatialScaleVector i) \ spatialScaleDomain i T ⊆ Ici 0)
  apply h.congr_fun _ (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)
  intro t ht
  have he : spatialScaleLogSum i t = ∑ j, Real.log (1 + t j) := by
    apply Finset.sum_congr rfl
    intro j _
    have htj : ↑0 ≤ t j := ht.1 j
    rw [max_eq_right htj]
  have hlog : 2 * Real.log T < ∑ j, Real.log (1 + t j) := by
    by_contra hh
    apply ht.2
    refine ⟨ht.1, ?_⟩
    change spatialScaleLogSum i t ≤ 2 * Real.log T
    rw [he]
    exact le_of_not_gt hh
  unfold strictLogScaleTail logScaleTail
  have hm : t ∈ {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} := hlog
  rw [Set.indicator_of_mem hm, ite_eq_left hlog.le]
theorem spatial_scale_complement_power_integral_le  (hn : 2 ≤ n) (i : Fin n)
    {b T : ℝ} (hb : (1 / 2 : ℝ) ≤ b) (hT : 1 ≤ T) :
    (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
      ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) ≤
      16 ^ (n - 1) * T ^ (-2 * b : ℝ) * (1 + Real.log T) ^ (n - 2) := by
  have hcard : Fintype.card (SpatialScaleIndex i) = (n - 2) + 1 := by
    rw [spatial_scale_index_card]
    omega
  have : 0 ≤ Real.log T := Real.log_nonneg hT
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have h_spatial_scale_complement_integral_eq : (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
      ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) =
      ∫ t : SpatialScaleVector i in Ici 0, strictLogScaleTail b (2 * Real.log T) t := by
    change (∫ t : SpatialScaleVector i in Ici 0 \ spatialScaleDomain i T,
      ∏ j, (1 + t j) ^ (-b - 1 : ℝ)) =
        ∫ t : SpatialScaleVector i in Ici 0,
          ({t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)}).indicator
            (logScaleTail b (2 * Real.log T)) t
    have hlogs : Measurable (fun t : SpatialScaleVector i => ∑ j, Real.log (1 + t j)) :=
      Finset.measurable_sum _ fun j _ => Real.measurable_log.comp
        (measurable_const.add (measurable_pi_apply j))
    have hm : MeasurableSet {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} :=
      measurableSet_lt measurable_const hlogs
    rw [integral_indicator hm, Measure.restrict_restrict hm]
    have hs : {t : SpatialScaleVector i | 2 * Real.log T < ∑ j, Real.log (1 + t j)} ∩ Ici 0 =
        Ici 0 \ spatialScaleDomain i T := by
      ext t
      constructor
      · rintro ⟨hlog, ht⟩
        change 2 * Real.log T < ∑ j, Real.log (1 + t j) at hlog
        refine ⟨ht, ?_⟩
        intro hD
        have he : spatialScaleLogSum i t = ∑ j, Real.log (1 + t j) := by
          unfold spatialScaleLogSum
          apply Finset.sum_congr rfl
          intro j _
          have htj : ↑0 ≤ t j := ht j
          rw [max_eq_right htj]
        rw [← he] at hlog
        exact (not_lt_of_ge hD.2) hlog
      · rintro ⟨ht, hD⟩
        refine ⟨?_, ht⟩
        by_contra h
        apply hD
        refine ⟨ht, ?_⟩
        change spatialScaleLogSum i t ≤ 2 * Real.log T
        unfold spatialScaleLogSum
        have hh : ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T := le_of_not_gt h
        convert hh using 1
        apply Finset.sum_congr rfl
        intro j _
        have htj : ↑0 ≤ t j := ht j
        rw [max_eq_right htj]
    rw [hs]
    apply setIntegral_congr_fun (measurableSet_Ici.diff (spatial_scale_domain_isClosed i T).measurableSet)
    intro t ht
    have hlog : 2 * Real.log T < ∑ j, Real.log (1 + t j) := by
      rw [← hs] at ht
      exact ht.1
    exact (if_pos hlog.le).symm
  rw [h_spatial_scale_complement_integral_eq]
  have h := strict_log_scale_tail_integral_le hcard hb (by linarith : 0 ≤ 2 * Real.log T)
  have he : Real.exp (-(b * (2 * Real.log T))) = T ^ (-2 * b : ℝ) := by
    rw [Real.rpow_def_of_pos hTpos]
    congr 1
    ring
  rw [he] at h
  have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 2 * Real.log T)
    (by linarith : 1 + 2 * Real.log T ≤ 2 * (1 + Real.log T)) (n - 2)
  have hconst : (8 : ℝ) ^ (n - 2 + 1) * 2 ^ (n - 2) ≤ 16 ^ (n - 1) := by
    have hn' : n - 2 + 1 = n - 1 := by omega
    rw [hn']
    calc
      _ ≤ 8 ^ (n - 1) * 2 ^ (n - 1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : n - 2 ≤ n - 1)) (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  have hh := mul_le_mul_of_nonneg_left (by simpa only [mul_pow] using hh)
    (by positivity : 0 ≤ (8 : ℝ) ^ (n - 2 + 1) * T ^ (-2 * b : ℝ))
  have hc := mul_le_mul_of_nonneg_right hconst
    (by positivity : 0 ≤ T ^ (-2 * b : ℝ) * (1 + Real.log T) ^ (n - 2))
  calc
    _ ≤ _ := h
    _ ≤ _ := by nlinarith [hh, hc]
end
section
variable {d D : ℕ}
abbrev GaussianPrimitiveIndex (d : ℕ) := (Fin d × Fin d) × (Bool × Bool) × Bool
abbrev GaussianPrimitiveMark (d : ℕ) := Covariate d × GaussianPrimitiveIndex d
def gaussianPrimitiveMeasure (d ) : Measure (GaussianPrimitiveMark d) :=
  (standardGaussianPi d).prod Measure.count
def gaussianTrig  (lam t : ℝ) (Z x : Covariate d) (s : Bool) : ℝ :=
  if s then Real.sin (gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z)
  else Real.cos (gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z)
theorem gaussianTrig_abs_le_one  (lam t : ℝ) (Z x : Covariate d) (s : Bool) :
    |gaussianTrig lam t Z x s| ≤ 1 := by
  cases s <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true]
  · exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  · exact abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
def gaussianAffinePolynomial  (a : Fin d) (s : Bool) : MvPolynomial (Fin d) ℝ :=
  if s then C (-8) * X a else C 2
def gaussianAffineFactor  (a : Fin d) (s : Bool) (y : Covariate d) : ℝ :=
  if s then 1 else y a / 2
theorem gaussianAffineFactor_abs_le_one  (a : Fin d) (s : Bool) (y : Covariate d)
    (hy : |y a| ≤ 2) : |gaussianAffineFactor a s y| ≤ 1 := by
  cases s
  · simp only [gaussianAffineFactor, Bool.false_eq_true, ite_false, abs_div,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa using hy)
  · simp [gaussianAffineFactor]
theorem spatialCardinalAffine_gaussian_coeff  (x y β) :
    (spatialCardinalAffine x y).coeff β =
      ∑ a : Fin d, (y a - x a) *
        ∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β := by
  have h_spatialCardinalAffine_gaussian_expansion : spatialCardinalAffine x y =
      ∑ a : Fin d, C (y a - x a) *
        ∑ s : Bool, C (gaussianAffineFactor a s y) * gaussianAffinePolynomial a s := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [Fintype.sum_bool, gaussianAffineFactor, gaussianAffinePolynomial,
      Bool.false_eq_true, ite_false, ite_true]
    rw [← C_mul]
    have hy : y a / 2 * 2 = y a := by ring
    rw [hy]
    simp only [C_1, one_mul]
    simp only [map_mul, map_neg]
    ring
  rw [h_spatialCardinalAffine_gaussian_expansion]
  simp only [coeff_sum, coeff_C_mul]
def gaussianPrimitiveLeft  (lam t : ℝ) (e : GaussianPrimitiveMark d) (x : Covariate d) : ℝ :=
  gaussianTrig lam t e.1 x e.2.2.2
def gaussianPrimitiveRight  (lam t : ℝ) (e : GaussianPrimitiveMark d) (y : Covariate d) : ℝ :=
  gaussianTrig lam t e.1 y e.2.2.2 *
    gaussianAffineFactor e.2.1.1 e.2.2.1.1 y * gaussianAffineFactor e.2.1.2 e.2.2.1.2 y
def gaussianPrimitiveAmplitude  (lam : ℝ) (e : GaussianPrimitiveMark d)
    (β β' : Fin d →₀ ℕ) : ℝ :=
  lam / 2 * gaussianHermite e.2.1.1 e.2.1.2 e.1 *
    (gaussianAffinePolynomial e.2.1.1 e.2.2.1.1).coeff β *
      (gaussianAffinePolynomial e.2.1.2 e.2.2.1.2).coeff β'
theorem gaussianPrimitiveAmplitude_measurable  (lam : ℝ) (β β' : Fin d →₀ ℕ) :
    Measurable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveAmplitude lam e β β') := by
  apply measurable_from_prod_countable_left
  intro h
  unfold gaussianPrimitiveAmplitude
  dsimp only
  have hm : Measurable (fun Z => gaussianHermite h.1.1 h.1.2 Z) :=
    measurable_const.sub ((measurable_pi_apply _).mul (measurable_pi_apply _))
  exact ((hm.const_mul _).mul_const _).mul_const _
theorem gaussianPrimitiveAmplitude_integrable  (lam β β') :
    Integrable (fun e : GaussianPrimitiveMark d => gaussianPrimitiveAmplitude lam e β β')
      (gaussianPrimitiveMeasure d) :=
  have h_gaussianPrimitiveAmplitude_slice_integrable (h) : Integrable (fun Z => gaussianPrimitiveAmplitude lam (Z, h) β β') (standardGaussianPi d) := by
    change Integrable (fun Z => lam / 2 * gaussianHermite h.1.1 h.1.2 Z *
      (gaussianAffinePolynomial h.1.1 h.2.1.1).coeff β *
      (gaussianAffinePolynomial h.1.2 h.2.1.2).coeff β') (standardGaussianPi d)
    exact (((gaussianHermite_integrable h.1.1 h.1.2).const_mul _).mul_const _).mul_const _
  joint_finite_integrable _ _
    (fun h => (gaussianPrimitiveAmplitude_measurable lam β β').comp
      (measurable_id.prodMk measurable_const))
    h_gaussianPrimitiveAmplitude_slice_integrable
theorem finite_injective_indicator_sum_le_one {I X : Type*} [Fintype I] [DecidableEq X]
    (f : I → X) (hf : Function.Injective f) (x : X) :
    (∑ i, if x = f i then (1 : ℝ) else 0) ≤ 1 := by
  classical
  by_cases hx : ∃ i, f i = x
  · obtain ⟨i, hi⟩ := hx
    have he (j : I) : x = f j ↔ j = i := by
      rw [← hi]
      exact ⟨fun h => (hf h).symm, fun h => by rw [h]⟩
    simp_rw [he]
    simp
  · have he (j : I) : x ≠ f j := by intro h; exact hx ⟨j, h.symm⟩
    simp only [ite_eq_right (he _), Finset.sum_const_zero]
    norm_num
theorem gaussianPrimitive_observable_integrable  (lam t x y β β') :
    Integrable (fun e => gaussianPrimitiveLeft lam t e x *
      gaussianPrimitiveRight lam t e y * gaussianPrimitiveAmplitude lam e β β')
      (gaussianPrimitiveMeasure d) := by
  let L := ∑ h : GaussianPrimitiveIndex d,
    |gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y|
  have h_gaussianPrimitiveLeft_measurable : Measurable (fun e => gaussianPrimitiveLeft lam t e x) := by
    apply measurable_from_prod_countable_left
    intro h
    change Measurable (fun Z => gaussianTrig lam t Z x h.2.2)
    cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
      unfold gaussianPhase <;> fun_prop
  have h_gaussianPrimitiveRight_measurable : Measurable (fun e => gaussianPrimitiveRight lam t e y) := by
    apply measurable_from_prod_countable_left
    intro h
    unfold gaussianPrimitiveRight
    dsimp only
    have hm : Measurable (fun Z => gaussianTrig lam t Z y h.2.2) := by
      cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
        unfold gaussianPhase <;> fun_prop
    exact (hm.mul_const _).mul_const _
  have hm : Measurable (fun e : GaussianPrimitiveMark d =>
      gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y) :=
    h_gaussianPrimitiveLeft_measurable.mul h_gaussianPrimitiveRight_measurable
  have hb (e : GaussianPrimitiveMark d) :
      ‖gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y‖ ≤ L := by
    unfold gaussianPrimitiveLeft gaussianPrimitiveRight
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
    have htrig := mul_le_mul (gaussianTrig_abs_le_one lam t e.1 x e.2.2.2)
      (gaussianTrig_abs_le_one lam t e.1 y e.2.2.2) (abs_nonneg _) (by norm_num)
    have hl : |gaussianAffineFactor e.2.1.1 e.2.2.1.1 y| *
        |gaussianAffineFactor e.2.1.2 e.2.2.1.2 y| ≤ L := by
      dsimp [L]
      rw [← abs_mul]
      exact Finset.single_le_sum (fun h _ => abs_nonneg
        (gaussianAffineFactor h.1.1 h.2.1.1 y * gaussianAffineFactor h.1.2 h.2.1.2 y))
        (Finset.mem_univ e.2)
    calc
      _ = |gaussianTrig lam t e.1 x e.2.2.2| * |gaussianTrig lam t e.1 y e.2.2.2| *
          (|gaussianAffineFactor e.2.1.1 e.2.2.1.1 y| * |gaussianAffineFactor e.2.1.2 e.2.2.1.2 y|) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_right htrig (mul_nonneg (abs_nonneg _) (abs_nonneg _))).trans
        (by simpa using hl)
  have hi := (gaussianPrimitiveAmplitude_integrable lam β β').mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)
  convert hi using 1
  funext e
  ring
theorem gaussianPrimitive_separated_exact  (lam t ) (hlam : 0 ≤ lam) (ht : 0 ≤ t)
    (x y β β') :
    t * lam ^ 2 * Real.exp (-t * lam * spatialSquaredDistance x y) *
      (spatialCardinalAffine x y).coeff β * (spatialCardinalAffine x y).coeff β' =
      ∫ e, gaussianPrimitiveLeft lam t e x * gaussianPrimitiveRight lam t e y *
        gaussianPrimitiveAmplitude lam e β β' ∂gaussianPrimitiveMeasure d := by
  rw [gaussianPrimitiveMeasure, integral_prod _ (gaussianPrimitive_observable_integrable lam t x y β β')]
  have h_gaussianPrimitive_finite_action (Z : Covariate d) (β : Fin d →₀ ℕ) (β' : Fin d →₀ ℕ) : (∑ h : GaussianPrimitiveIndex d,
      gaussianPrimitiveLeft lam t (Z, h) x * gaussianPrimitiveRight lam t (Z, h) y *
        gaussianPrimitiveAmplitude lam (Z, h) β β') =
      lam / 2 * ∑ a : Fin d, ∑ b : Fin d,
        gaussianHermite a b Z *
          (∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
          (∑ s : Bool, gaussianAffineFactor b s y * (gaussianAffinePolynomial b s).coeff β') *
          Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) := by
    classical
    simp only [Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    have hphase (s s' : Bool) :
        (∑ p : Bool, gaussianPrimitiveLeft lam t (Z, ((a, b), ((s, s'), p))) x *
          gaussianPrimitiveRight lam t (Z, ((a, b), ((s, s'), p))) y *
            gaussianPrimitiveAmplitude lam (Z, ((a, b), ((s, s'), p))) β β') =
        (lam / 2 * gaussianHermite a b Z * Real.cos
          (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) *
            gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β *
            (gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β') := by
      have h_gaussianTrig_cos_difference : Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) =
        ∑ s : Bool, gaussianTrig lam t Z x s * gaussianTrig lam t Z y s := by
        have he : gaussianPhase (gaussianSpatialFrequency lam t x y) Z =
            gaussianPhase (fun l => Real.sqrt (2 * lam * t) * y l) Z -
            gaussianPhase (fun l => Real.sqrt (2 * lam * t) * x l) Z := by
          simp only [gaussianPhase, gaussianSpatialFrequency, Finset.sum_sub_distrib]
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro l hl
          ring
        rw [he, Real.cos_sub]
        simp only [Fintype.sum_bool, gaussianTrig, Bool.false_eq_true, ite_false, ite_true]
        ring
      rw [h_gaussianTrig_cos_difference]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      unfold gaussianPrimitiveLeft gaussianPrimitiveRight gaussianPrimitiveAmplitude
      dsimp only
      ring
    simp_rw [hphase]
    have he := Fintype.sum_mul_sum
      (fun s => gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β)
      (fun s' => gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β')
    calc
      _ = (lam / 2 * gaussianHermite a b Z * Real.cos
          (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) *
          (∑ s : Bool, ∑ s' : Bool,
            (gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β) *
            (gaussianAffineFactor b s' y * (gaussianAffinePolynomial b s').coeff β')) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro s hs
        apply Finset.sum_congr rfl
        intro s' hs'
        ring
      _ = _ := by rw [← he]; ring
  simp only [integral_count, h_gaussianPrimitive_finite_action]
  let va := fun a => ∑ s : Bool, gaussianAffineFactor a s y * (gaussianAffinePolynomial a s).coeff β
  let vb := fun b => ∑ s : Bool, gaussianAffineFactor b s y * (gaussianAffinePolynomial b s).coeff β'
  have hi (a b : Fin d) : Integrable (fun Z => gaussianHermite a b Z * va a * vb b *
      Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) (standardGaussianPi d) := by
    have hm : Measurable (fun Z : Covariate d => Real.cos
        (gaussianPhase (gaussianSpatialFrequency lam t x y) Z)) := by
      unfold gaussianPhase
      fun_prop
    exact (((gaussianHermite_integrable a b).mul_const (va a)).mul_const (vb b)).mul_bdd
      hm.aestronglyMeasurable (Filter.Eventually.of_forall (fun Z => by
        rw [Real.norm_eq_abs]
        exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩))
  change _ = ∫ Z, lam / 2 * ∑ a : Fin d, ∑ b : Fin d,
    gaussianHermite a b Z * va a * vb b * Real.cos
      (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) ∂standardGaussianPi d
  rw [integral_const_mul, integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hi a b))]
  simp_rw [integral_finsetSum _ (fun b _ => hi _ b)]
  rw [spatialCardinalAffine_gaussian_coeff, spatialCardinalAffine_gaussian_coeff]
  have h_gaussianAffine_coefficient_bilinear : t * lam ^ 2 * Real.exp (-t * lam * spatialSquaredDistance x y) *
      (∑ a, (y a - x a) * va a) * (∑ b, (y b - x b) * vb b) =
      lam / 2 * ∑ a : Fin d, ∑ b : Fin d,
        ∫ Z, gaussianHermite a b Z * va a * vb b *
          Real.cos (gaussianPhase (gaussianSpatialFrequency lam t x y) Z) ∂standardGaussianPi d := by
    have h_gaussianSpatialFrequency_squared : (∑ l, (gaussianSpatialFrequency lam t x y l) ^ 2) =
        2 * lam * t * spatialSquaredDistance x y := by
      unfold gaussianSpatialFrequency spatialSquaredDistance
      simp_rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * lam * t)]
      rw [Finset.mul_sum]
    simp_rw [standardGaussian_hermite_cos_integral_const,
      h_gaussianSpatialFrequency_squared]
    have he : -(2 * lam * t * spatialSquaredDistance x y) / 2 =
        -(t * lam * spatialSquaredDistance x y) := by ring
    rw [he]
    unfold gaussianSpatialFrequency
    simp only [Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    calc
      _ = lam / 2 * (2 * lam * t) * (y a - x a) * (y b - x b) * va a * vb b *
          Real.exp (-(t * lam * spatialSquaredDistance x y)) := by ring
      _ = lam / 2 * (Real.sqrt (2 * lam * t) ^ 2) * (y a - x a) * (y b - x b) * va a * vb b *
          Real.exp (-(t * lam * spatialSquaredDistance x y)) := by rw [(Real.sq_sqrt (by positivity : 0 ≤ 2 * lam * t))]
      _ = _ := by ring
  exact h_gaussianAffine_coefficient_bilinear
theorem gaussianPrimitiveMeasure_finite (d ) : IsFiniteMeasure (gaussianPrimitiveMeasure d) := by
  unfold gaussianPrimitiveMeasure
  infer_instance
def gaussianAffineExponent  (a : Fin d) (s : Bool) : Fin d →₀ ℕ :=
  if s then Finsupp.single a 1 else 0
def gaussianAffineCoefficient (s : Bool) : ℝ := if s then -8 else 2
theorem gaussianAffinePolynomial_monomial  (a : Fin d) (s : Bool) :
    gaussianAffinePolynomial a s =
      monomial (gaussianAffineExponent a s) (gaussianAffineCoefficient s) := by
  cases s <;> simp only [gaussianAffinePolynomial, gaussianAffineExponent, gaussianAffineCoefficient,
    Bool.false_eq_true, ite_false, ite_true, C_apply, X, monomial_mul_monomial,
    zero_add, mul_one]
def gaussianPolynomialProduct  [Fintype κ] 
    (a : κ → Fin d) (s : κ → Bool) : MvPolynomial (Fin d) ℝ := ∏ i, gaussianAffinePolynomial (a i) (s i)
theorem gaussianPolynomialProduct_monomial  [Fintype κ] 
    (a : κ → Fin d) (s : κ → Bool) :
    gaussianPolynomialProduct a s =
      monomial (∑ i, gaussianAffineExponent (a i) (s i)) (∏ i, gaussianAffineCoefficient (s i)) := by
  unfold gaussianPolynomialProduct
  simp_rw [gaussianAffinePolynomial_monomial]
  exact (monomial_sum_prod _ _ _).symm
theorem gaussianAffineCoefficient_abs_le_eight (s ) : |gaussianAffineCoefficient s| ≤ 8 := by
  cases s <;> norm_num [gaussianAffineCoefficient]
theorem gaussianPolynomialProduct_frame_cost  [Fintype κ] 
    (a : κ → Fin d) (s : κ → Bool) :
    (∑ β : HighFrameIndex d D, |highFrameCoefficients (gaussianPolynomialProduct a s) β|) ≤
      ↑8 ^ Fintype.card κ := by
  have hinj : Function.Injective (fun β : HighFrameIndex d D => polynomialBoxExponent β.val) := by
    intro β β' h
    exact Subtype.ext (polynomial_box_exponent_injective h)
  rw [gaussianPolynomialProduct_monomial]
  have he (β : HighFrameIndex d D) :
      |highFrameCoefficients (monomial (∑ i, gaussianAffineExponent (a i) (s i))
        (∏ i, gaussianAffineCoefficient (s i))) β| =
      |∏ i, gaussianAffineCoefficient (s i)| *
        (if (∑ i, gaussianAffineExponent (a i) (s i)) = polynomialBoxExponent β.val then 1 else 0) := by
    simp only [highFrameCoefficients, coeff_monomial]
    split_ifs <;> simp
  simp_rw [he]
  rw [← Finset.mul_sum]
  have h := finite_injective_indicator_sum_le_one _ hinj (∑ i, gaussianAffineExponent (a i) (s i))
  have h_gaussianPolynomialProduct_coefficient_bound : |∏ i, gaussianAffineCoefficient (s i)| ≤ (8 : ℝ) ^ Fintype.card κ := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : κ, (8 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun i _ => gaussianAffineCoefficient_abs_le_eight (s i))
      _ = _ := by simp
  calc
    _ ≤ |∏ i, gaussianAffineCoefficient (s i)| * 1 := mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using h_gaussianPolynomialProduct_coefficient_bound
theorem gaussianPolynomialProduct_rankone_cost  [Fintype κ] [Fintype κ']
     (a ) (s : κ → Bool) (b : κ' → Fin d) (s' : κ' → Bool) (c : ℝ) :
    (∑ β : HighFrameIndex d D, ∑ β' : HighFrameIndex d D,
      |c * highFrameCoefficients (gaussianPolynomialProduct a s) β *
        highFrameCoefficients (gaussianPolynomialProduct b s') β'|) ≤
      |c| * 8 ^ (Fintype.card κ + Fintype.card κ') := by
  have he : (∑ β : HighFrameIndex d D, ∑ β' : HighFrameIndex d D,
      |c * highFrameCoefficients (gaussianPolynomialProduct a s) β *
        highFrameCoefficients (gaussianPolynomialProduct b s') β'|) =
      |c| * (∑ β : HighFrameIndex d D, |highFrameCoefficients (gaussianPolynomialProduct a s) β|) *
      (∑ β' : HighFrameIndex d D, |highFrameCoefficients (gaussianPolynomialProduct b s') β'|) := by
    simp only [abs_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [he, pow_add, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg c)
  exact mul_le_mul (gaussianPolynomialProduct_frame_cost a s)
    (gaussianPolynomialProduct_frame_cost b s')
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by positivity)
instance gaussianPrimitiveMeasure_isFinite (d : ℕ) : IsFiniteMeasure (gaussianPrimitiveMeasure d) :=
  gaussianPrimitiveMeasure_finite d
def gaussianPrimitiveScalar (d ) (lam : ℝ) (e : GaussianPrimitiveMark d) : ℝ :=
  lam / 2 * gaussianHermite e.2.1.1 e.2.1.2 e.1
theorem gaussianPrimitiveScalar_measurable (d lam) :
    Measurable (gaussianPrimitiveScalar d lam) := by
  apply measurable_from_prod_countable_left
  intro h
  change Measurable (fun Z => lam / 2 * gaussianHermite h.1.1 h.1.2 Z)
  have hm : Measurable (fun Z => gaussianHermite h.1.1 h.1.2 Z) :=
    measurable_const.sub ((measurable_pi_apply _).mul (measurable_pi_apply _))
  exact hm.const_mul _
theorem gaussianPrimitiveScalar_integrable (d lam) :
    Integrable (gaussianPrimitiveScalar d lam) (gaussianPrimitiveMeasure d) :=
  have h_gaussianPrimitiveScalar_slice_integrable (h) : Integrable (fun Z => gaussianPrimitiveScalar d lam (Z, h)) (standardGaussianPi d) := by
    change Integrable (fun Z => lam / 2 * gaussianHermite h.1.1 h.1.2 Z) _
    exact (gaussianHermite_integrable h.1.1 h.1.2).const_mul _
  joint_finite_integrable _ _
    (fun h => (gaussianPrimitiveScalar_measurable d lam).comp (measurable_id.prodMk measurable_const))
    h_gaussianPrimitiveScalar_slice_integrable
abbrev GaussianTensorMark (κ : Type*) (d : ℕ) := κ → GaussianPrimitiveMark d
def gaussianTensorMeasure (κ ) [Fintype κ] (d ) : Measure (GaussianTensorMark κ d) :=
  Measure.pi (fun _ => gaussianPrimitiveMeasure d)
def gaussianTensorScalar  [Fintype κ]  (lam : ℝ) (e : GaussianTensorMark κ d) : ℝ :=
  ∏ i, gaussianPrimitiveScalar d lam (e i)
def gaussianTensorLeftPolynomial  [Fintype κ]  (e : GaussianTensorMark κ d) :
    MvPolynomial (Fin d) ℝ :=
  gaussianPolynomialProduct (fun i => (e i).2.1.1) (fun i => (e i).2.2.1.1)
def gaussianTensorRightPolynomial  [Fintype κ]  (e : GaussianTensorMark κ d) :
    MvPolynomial (Fin d) ℝ :=
  gaussianPolynomialProduct (fun i => (e i).2.1.2) (fun i => (e i).2.2.1.2)
def gaussianTensorFrameAmplitude  [Fintype κ]  (lam : ℝ)
    (e : GaussianTensorMark κ d) (β β' : HighFrameIndex d D) : ℝ :=
  gaussianTensorScalar lam e * highFrameCoefficients (gaussianTensorLeftPolynomial e) β *
    highFrameCoefficients (gaussianTensorRightPolynomial e) β'
theorem gaussianTensorMeasure_finite (κ ) [Fintype κ] (d ) :
    IsFiniteMeasure (gaussianTensorMeasure κ d) := by
  letI : IsFiniteMeasure (gaussianPrimitiveMeasure d) := gaussianPrimitiveMeasure_finite d
  unfold gaussianTensorMeasure
  infer_instance
theorem gaussianTensorScalar_integrable  [Fintype κ]  (lam ) :
    Integrable (gaussianTensorScalar (κ := κ) (d := d) lam) (gaussianTensorMeasure κ d) :=
  Integrable.fintype_prod (fun _ => gaussianPrimitiveScalar_integrable d lam)
theorem gaussianTensorPolynomial_coeff_measurable  [Fintype κ] 
    (a : GaussianPrimitiveIndex d → Fin d) (s : GaussianPrimitiveIndex d → Bool) (β : Fin d →₀ ℕ) :
    Measurable (fun e : GaussianTensorMark κ d =>
      (gaussianPolynomialProduct (fun i => a (e i).2) (fun i => s (e i).2)).coeff β) := by
  have hf : Measurable (fun h : κ → GaussianPrimitiveIndex d =>
      (gaussianPolynomialProduct (fun i => a (h i)) (fun i => s (h i))).coeff β) := measurable_of_countable _
  have hg : Measurable (fun e : GaussianTensorMark κ d => fun i => (e i).2) :=
    measurable_pi_iff.mpr (fun i => measurable_snd.comp (measurable_pi_apply i))
  exact hf.comp hg
theorem gaussianTensorFrameAmplitude_measurable {κ : Type*} [Fintype κ]  (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Measurable (fun e : GaussianTensorMark κ d => gaussianTensorFrameAmplitude lam e β β') := by
  have hl := gaussianTensorPolynomial_coeff_measurable (κ := κ) (d := d)
    (fun h => h.1.1) (fun h => h.2.1.1) (polynomialBoxExponent β.val)
  have hr := gaussianTensorPolynomial_coeff_measurable (κ := κ) (d := d)
    (fun h => h.1.2) (fun h => h.2.1.2) (polynomialBoxExponent β'.val)
  have h_gaussianTensorScalar_measurable : Measurable (gaussianTensorScalar (κ := κ) (d := d) lam) := Finset.measurable_fun_prod _ (fun i _ =>
    (gaussianPrimitiveScalar_measurable d lam).comp (measurable_pi_apply i))
  exact (h_gaussianTensorScalar_measurable.mul hl).mul hr
theorem gaussianTensorFrameAmplitude_cost_bound  [Fintype κ]  (lam )
    (e : GaussianTensorMark κ d) :
    separatedMatrixCost (gaussianTensorFrameAmplitude (D := D) lam) e ≤
      |gaussianTensorScalar lam e| * ↑8 ^ (2 * Fintype.card κ) := by
  have h := gaussianPolynomialProduct_rankone_cost (D := D)
    (fun i => (e i).2.1.1) (fun i => (e i).2.2.1.1)
    (fun i => (e i).2.1.2) (fun i => (e i).2.2.1.2) (gaussianTensorScalar lam e)
  simpa only [two_mul, separatedMatrixCost, gaussianTensorFrameAmplitude,
    gaussianTensorLeftPolynomial, gaussianTensorRightPolynomial] using h
theorem gaussianTensorFrameAmplitude_cost_integrable  [Fintype κ]  (lam : ℝ) :
    Integrable (separatedMatrixCost (gaussianTensorFrameAmplitude (κ := κ) (d := d) (D := D) lam))
      (gaussianTensorMeasure κ d) := by
  have h_gaussianTensorFrameAmplitude_cost_measurable : Measurable (separatedMatrixCost (gaussianTensorFrameAmplitude (κ := κ) (d := d) (D := D) lam)) := by
    exact Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
      (fun β' _ => (gaussianTensorFrameAmplitude_measurable lam β β').abs))
  apply ((gaussianTensorScalar_integrable (κ := κ) (d := d) lam).abs.mul_const
    (↑8 ^ (2 * Fintype.card κ))).mono'
    h_gaussianTensorFrameAmplitude_cost_measurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
    (fun β _ => Finset.sum_nonneg (fun β' _ => abs_nonneg _)))]
  exact gaussianTensorFrameAmplitude_cost_bound lam e
def gaussianTensorAmplitude  [Fintype κ]  (lam : ℝ)
    (e : GaussianTensorMark κ d) (β β' : Fin d →₀ ℕ) : ℝ :=
  gaussianTensorScalar lam e * (gaussianTensorLeftPolynomial e).coeff β *
    (gaussianTensorRightPolynomial e).coeff β'
def gaussianTensorObservable  [Fintype κ]  (lam : ℝ) (t : κ → ℝ)
    (x y : κ → Covariate d) (e : GaussianTensorMark κ d) : ℝ :=
  ∏ i, gaussianPrimitiveLeft lam (t i) (e i) (x i) * gaussianPrimitiveRight lam (t i) (e i) (y i)
def realMatrixSymmetrize  (A : I → I → ℝ) (i j : I) : ℝ := (A i j + A j i) / 2
theorem separatedMatrixCost_symmetrize_le {E I : Type*} [Fintype I] [DecidableEq I]
    (A : E → I → I → ℝ) (e : E) :
    separatedMatrixCost (fun e => realMatrixSymmetrize (A e)) e ≤ separatedMatrixCost A e := by
  have hp (i j : I) : |realMatrixSymmetrize (A e) i j| ≤ (|A e i j| + |A e j i|) / 2 := by
    unfold realMatrixSymmetrize
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right (abs_add_le _ _) (by norm_num)
  calc
    _ ≤ ∑ i : I, ∑ j : I, (|A e i j| + |A e j i|) / 2 := Finset.sum_le_sum
      (fun i _ => Finset.sum_le_sum (fun j _ => hp i j))
    _ = separatedMatrixCost A e := by
      simp only [← Finset.sum_div, Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => |A e j i|)]
      unfold separatedMatrixCost
      ring
def gaussianTensorSymmetricAmplitude  [Fintype κ]  (lam : ℝ)
    (e : GaussianTensorMark κ d) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  realMatrixSymmetrize (gaussianTensorFrameAmplitude lam e)
theorem gaussianTensorSymmetricAmplitude_measurable  [Fintype κ]  (lam )
    (β β' : HighFrameIndex d D) :
    Measurable (fun e : GaussianTensorMark κ d => gaussianTensorSymmetricAmplitude lam e β β') :=
  ((gaussianTensorFrameAmplitude_measurable lam β β').add
    (gaussianTensorFrameAmplitude_measurable lam β' β)).div_const 2
theorem gaussianTensorSymmetricAmplitude_cost_integrable  [Fintype κ]  (lam : ℝ) :
    Integrable (separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := κ) (d := d) (D := D) lam))
      (gaussianTensorMeasure κ d) := by
  have hm : Measurable (separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := κ) (d := d) (D := D) lam)) :=
    Finset.measurable_fun_sum _ (fun β _ => Finset.measurable_fun_sum _
      (fun β' _ => (gaussianTensorSymmetricAmplitude_measurable lam β β').abs))
  apply (gaussianTensorFrameAmplitude_cost_integrable (κ := κ) (d := d) (D := D) lam).mono'
    hm.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro e
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
    (fun β _ => Finset.sum_nonneg (fun β' _ => abs_nonneg _)))]
  exact separatedMatrixCost_symmetrize_le _ e
theorem gaussianTensorSymmetricAmplitude_integrated_cost  [Fintype κ]  (lam ) :
    (∫ e, separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := κ) (d := d) (D := D) lam) e
      ∂gaussianTensorMeasure κ d) ≤ (512 * |lam| * ↑d ^ 2) ^ Fintype.card κ :=
  have h_gaussianTensorFrameAmplitude_integrated_cost : (∫ e, separatedMatrixCost (gaussianTensorFrameAmplitude (κ := κ) (d := d) (D := D) lam) e
      ∂gaussianTensorMeasure κ d) ≤ (512 * |lam| * ↑d ^ 2) ^ Fintype.card κ := by
    have hm := integral_mono (gaussianTensorFrameAmplitude_cost_integrable (κ := κ) (d := d) (D := D) lam)
      ((gaussianTensorScalar_integrable (κ := κ) (d := d) lam).abs.mul_const (↑8 ^ (2 * Fintype.card κ)))
      (gaussianTensorFrameAmplitude_cost_bound lam)
    rw [integral_mul_const] at hm
    have h_gaussianTensorScalar_abs_integral : (∫ e, |gaussianTensorScalar (κ := κ) (d := d) lam e| ∂gaussianTensorMeasure κ d) ≤
        (8 * |lam| * d ^ 2) ^ Fintype.card κ := by
      unfold gaussianTensorScalar gaussianTensorMeasure
      simp only [Finset.abs_prod]
      rw [integral_fintype_prod_eq_prod (fun (_ : κ) e => |gaussianPrimitiveScalar d lam e|)]
      have h_gaussianPrimitiveScalar_abs_integral : (∫ e, |gaussianPrimitiveScalar d lam e| ∂gaussianPrimitiveMeasure d) ≤
          8 * |lam| * d ^ 2 := by
        have hs (h : GaussianPrimitiveIndex d) :
            (∫ Z, |gaussianPrimitiveScalar d lam (Z, h)| ∂standardGaussianPi d) ≤ |lam| := by
          change (∫ Z, |lam / 2 * gaussianHermite h.1.1 h.1.2 Z| ∂standardGaussianPi d) ≤ |lam|
          simp only [abs_mul, integral_const_mul]
          have h_standardGaussian_hermite_abs_integral_le_two : (∫ Z, |gaussianHermite h.1.1 h.1.2 Z| ∂standardGaussianPi d) ≤ 2 := by
            have ha : Integrable (fun Z => (Z h.1.1) ^ 2) (standardGaussianPi d) := by
              simpa only [pow_two] using standardGaussian_cross_integrable h.1.1 h.1.1
            have hb : Integrable (fun Z => (Z h.1.2) ^ 2) (standardGaussianPi d) := by
              simpa only [pow_two] using standardGaussian_cross_integrable h.1.2 h.1.2
            have hi : Integrable (fun Z => 1 + ((Z h.1.1) ^ 2 + (Z h.1.2) ^ 2) / 2)
                (standardGaussianPi d) := (integrable_const 1).add ((ha.add hb).div_const 2)
            have hdiv : Integrable (fun Z => ((Z h.1.1) ^ 2 + (Z h.1.2) ^ 2) / 2)
                (standardGaussianPi d) := (ha.add hb).div_const 2
            have hm := integral_mono (gaussianHermite_integrable h.1.1 h.1.2).abs hi (fun Z => by
              have hδ : |(if h.1.1 = h.1.2 then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
              exact (abs_sub _ _).trans (add_le_add hδ (by rw [abs_mul]; nlinarith [sq_nonneg (|Z h.1.1| - |Z h.1.2|), sq_abs (Z h.1.1), sq_abs (Z h.1.2)])))
            rw [integral_add (integrable_const 1) hdiv, integral_div,
              integral_add ha hb, standardGaussian_coordinate_square_integral,
              standardGaussian_coordinate_square_integral] at hm
            norm_num at hm
            exact hm
          have hm := mul_le_mul_of_nonneg_left h_standardGaussian_hermite_abs_integral_le_two
            (abs_nonneg (lam / 2))
          rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hm ⊢
          exact hm.trans_eq (by ring)
        rw [gaussianPrimitiveMeasure, integral_prod_symm _ (gaussianPrimitiveScalar_integrable d lam).abs,
          integral_count]
        have hm := Finset.sum_le_sum (s := Finset.univ) (fun h _ => hs h)
        convert hm using 1 <;> simp [GaussianPrimitiveIndex, Fintype.card_prod, pow_two] <;> ring
      calc
        _ ≤ ∏ _i : κ, (8 * |lam| * d ^ 2) := Finset.prod_le_prod₀
          (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
          (fun _ _ => h_gaussianPrimitiveScalar_abs_integral)
        _ = _ := by simp
    have h := mul_le_mul_of_nonneg_right h_gaussianTensorScalar_abs_integral
      (by positivity : 0 ≤ (8 : ℝ) ^ (2 * Fintype.card κ))
    apply hm.trans
    apply h.trans_eq
    rw [pow_mul, ← mul_pow]
    congr 1
    ring
  (integral_mono (gaussianTensorSymmetricAmplitude_cost_integrable lam)
    (gaussianTensorFrameAmplitude_cost_integrable lam)
    (separatedMatrixCost_symmetrize_le _)).trans h_gaussianTensorFrameAmplitude_integrated_cost
end
variable {n d D : ℕ} {T : ℝ}
section
variable {σ E F : Type*} [DecidableEq σ] [MeasurableSpace E] [MeasurableSpace F]
def polynomialPairMoment (w : E → ℝ) (P P' : E → MvPolynomial σ ℝ)
    (β β' : σ →₀ ℕ) (e : E) : ℝ := w e * (P e).coeff β * (P' e).coeff β'
theorem polynomialPairMoment_mul_expansion
    (w v P P' Q Q') (β β' : σ →₀ ℕ) (z : E × F) :
    polynomialPairMoment (fun z : E × F => w z.1 * v z.2)
      (fun z => P z.1 * Q z.2) (fun z => P' z.1 * Q' z.2) β β' z =
      ∑ b ∈ _root_.Finset.HasAntidiagonal.antidiagonal β,
        ∑ b' ∈ _root_.Finset.HasAntidiagonal.antidiagonal β',
        polynomialPairMoment w P P' b.1 b'.1 z.1 *
          polynomialPairMoment v Q Q' b.2 b'.2 z.2 := by
  unfold polynomialPairMoment
  rw [coeff_mul, coeff_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro b' hb'
  ring
theorem polynomialPairMoment_product_integrable
    (μ : Measure E) (ν : Measure F) [SigmaFinite μ] [SigmaFinite ν]
    (w : E → ℝ) (v : F → ℝ) (P P' : E → MvPolynomial σ ℝ)
    (Q Q' : F → MvPolynomial σ ℝ)
    (hP : ∀ β β', Integrable (polynomialPairMoment w P P' β β') μ)
    (hQ : ∀ β β', Integrable (polynomialPairMoment v Q Q' β β') ν)
    (β β' : σ →₀ ℕ) :
    Integrable (polynomialPairMoment (fun z : E × F => w z.1 * v z.2)
      (fun z => P z.1 * Q z.2) (fun z => P' z.1 * Q' z.2) β β') (μ.prod ν) := by
  change Integrable (fun z : E × F => polynomialPairMoment
    (fun z : E × F => w z.1 * v z.2) (fun z => P z.1 * Q z.2)
    (fun z => P' z.1 * Q' z.2) β β' z) (μ.prod ν)
  simp_rw [polynomialPairMoment_mul_expansion]
  exact integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun b' _ =>
    (hP b.1 b'.1).mul_prod (hQ b.2 b'.2)
theorem polynomialPairMoment_product_integral
    (μ : Measure E) (ν ) [SigmaFinite μ] [SigmaFinite ν]
    (w v P P' Q Q')
    (hP : ∀ β β', Integrable (polynomialPairMoment w P P' β β') μ)
    (hQ : ∀ β β', Integrable (polynomialPairMoment v Q Q' β β') ν)
    (p p' q q' : MvPolynomial σ ℝ) (a b )
    (hEP : ∀ β β', (∫ e, polynomialPairMoment w P P' β β' e ∂μ) =
      a * p.coeff β * p'.coeff β')
    (hEQ : ∀ β β', (∫ e, polynomialPairMoment v Q Q' β β' e ∂ν) =
      b * q.coeff β * q'.coeff β') (β β' ) :
    (∫ z, polynomialPairMoment (fun z : E × F => w z.1 * v z.2)
      (fun z => P z.1 * Q z.2) (fun z => P' z.1 * Q' z.2) β β' z ∂μ.prod ν) =
      a * b * (p * q).coeff β * (p' * q').coeff β' := by
  simp_rw [polynomialPairMoment_mul_expansion]
  rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ fun c' _ =>
    (hP c.1 c'.1).mul_prod (hQ c.2 c'.2))]
  simp_rw [integral_finsetSum _ (fun (c' : (σ →₀ ℕ) × (σ →₀ ℕ)) _ =>
    (hP _ c'.1).mul_prod (hQ _ c'.2)), integral_prod_mul, hEP, hEQ]
  rw [coeff_mul, coeff_mul]
  simp only [Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro c' hc'
  ring
def tensorPolynomialPairMoment  (w : Fin n → E → ℝ)
    (P P' : Fin n → E → MvPolynomial σ ℝ) (β β' : σ →₀ ℕ)
    (e : Fin n → E) : ℝ :=
  (∏ j, w j (e j)) * (∏ j, P j (e j)).coeff β * (∏ j, P' j (e j)).coeff β'
theorem tensorPolynomialPairMoment_fin
    (μ : Measure E) [SigmaFinite μ] (n w P P')
    (p p' : Fin n → MvPolynomial σ ℝ) (a : Fin n → ℝ)
    (hi : ∀ j β β', Integrable (polynomialPairMoment (w j) (P j) (P' j) β β') μ)
    (he : ∀ j β β', (∫ e, polynomialPairMoment (w j) (P j) (P' j) β β' e ∂μ) =
      a j * (p j).coeff β * (p' j).coeff β') :
    ∀ β β', Integrable (tensorPolynomialPairMoment w P P' β β') (Measure.pi (fun _ => μ)) ∧
      (∫ e, tensorPolynomialPairMoment w P P' β β' e ∂Measure.pi (fun _ => μ)) =
        (∏ j, a j) * (∏ j, p j).coeff β * (∏ j, p' j).coeff β' := by
  induction n with
  | zero =>
    intro β β'
    have hprob : IsProbabilityMeasure (Measure.pi (fun _ : Fin 0 => μ)) := by
      constructor
      rw [Measure.pi_empty_univ]
    let _ := hprob
    constructor
    · change Integrable (fun e : Fin 0 → E => tensorPolynomialPairMoment w P P' β β' e) _
      simp only [tensorPolynomialPairMoment, Finset.univ_eq_empty, Finset.prod_empty]
      exact integrable_const _
    · simp only [tensorPolynomialPairMoment, Finset.univ_eq_empty, Finset.prod_empty,
        integral_const, probReal_univ, one_smul]
  | succ n ih =>
    intro β β'
    let W (x : Fin n → E) := ∏ j, w j.succ (x j)
    let Q (x : Fin n → E) := ∏ j, P j.succ (x j)
    let Q' (x : Fin n → E) := ∏ j, P' j.succ (x j)
    have htail := ih (fun j => w j.succ) (fun j => P j.succ) (fun j => P' j.succ)
      (fun j => p j.succ) (fun j => p' j.succ) (fun j => a j.succ)
      (fun j => hi j.succ) (fun j => he j.succ)
    have hiTail  := fun b b' => (htail b b').1
    let G := polynomialPairMoment (fun z : E × (Fin n → E) => w 0 z.1 * W z.2)
      (fun z => P 0 z.1 * Q z.2) (fun z => P' 0 z.1 * Q' z.2) β β'
    have hGi  :=
      polynomialPairMoment_product_integrable μ _ (w 0) W (P 0) (P' 0) Q Q'
        (hi 0) hiTail β β'
    have hGe  :=
      polynomialPairMoment_product_integral μ _ (w 0) W (P 0) (P' 0) Q Q'
        (hi 0) hiTail (p 0) (p' 0) (∏ j : Fin n, p j.succ) (∏ j : Fin n, p' j.succ)
        (a 0) (∏ j : Fin n, a j.succ) (he 0) (fun b b' => (htail b b').2) β β'
    have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) 0).symm
    have hcomp : (tensorPolynomialPairMoment w P P' β β') ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm = G := by
      funext z
      simp only [Function.comp_def, tensorPolynomialPairMoment,
        MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
        Fin.prod_univ_succ, Fin.insertNth_zero, Fin.zero_succAbove, G, W, Q, Q',
        polynomialPairMoment, Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ, cast_eq]
    constructor
    · rw [← hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)]
      rw [hcomp]
      exact hGi
    · rw [← hmp.integral_comp']
      change (∫ x, ((tensorPolynomialPairMoment w P P' β β') ∘
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) 0).symm) x
        ∂μ.prod (Measure.pi (fun _ : Fin n => μ))) = _
      rw [hcomp, hGe]
      simp only [Fin.prod_univ_succ]
def tensorPolynomialPairMoment_fintype  [Fintype κ]
    (w : κ → E → ℝ) (P P' : κ → E → MvPolynomial σ ℝ)
    (β β' : σ →₀ ℕ) (e : κ → E) : ℝ :=
  (∏ j, w j (e j)) * (∏ j, P j (e j)).coeff β * (∏ j, P' j (e j)).coeff β'
theorem tensorPolynomialPairMoment_fintype_integral  [Fintype κ]
    (μ ) [SigmaFinite μ]
    (w ) (P P' : κ → E → MvPolynomial σ ℝ)
    (p p' : κ → MvPolynomial σ ℝ) (a : κ → ℝ)
    (hi : ∀ j β β', Integrable (polynomialPairMoment (w j) (P j) (P' j) β β') μ)
    (he : ∀ j β β', (∫ e, polynomialPairMoment (w j) (P j) (P' j) β β' e ∂μ) =
      a j * (p j).coeff β * (p' j).coeff β') (β β' : σ →₀ ℕ) :
    Integrable (tensorPolynomialPairMoment_fintype w P P' β β') (Measure.pi (fun _ => μ)) ∧
      (∫ e, tensorPolynomialPairMoment_fintype w P P' β β' e ∂Measure.pi (fun _ => μ)) =
        (∏ j, a j) * (∏ j, p j).coeff β * (∏ j, p' j).coeff β' := by
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  have h := tensorPolynomialPairMoment_fin μ (Fintype.card κ)
    (fun j => w (e j)) (fun j => P (e j)) (fun j => P' (e j))
    (fun j => p (e j)) (fun j => p' (e j)) (fun j => a (e j))
    (fun j => hi (e j)) (fun j => he (e j)) β β'
  have hmp := measurePreserving_piCongrLeft (fun _ : κ => μ) e
  have hcomp : (tensorPolynomialPairMoment_fintype w P P' β β') ∘
      MeasurableEquiv.piCongrLeft (fun _ : κ => E) e =
      tensorPolynomialPairMoment (fun j => w (e j)) (fun j => P (e j))
        (fun j => P' (e j)) β β' := by
    funext x
    simp only [Function.comp_def, tensorPolynomialPairMoment_fintype,
      tensorPolynomialPairMoment, ← e.prod_comp, MeasurableEquiv.coe_piCongrLeft,
      Equiv.piCongrLeft_apply_apply]
  constructor
  · rw [← hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _), hcomp]
    exact h.1
  · rw [← hmp.integral_comp']
    change (∫ x, ((tensorPolynomialPairMoment_fintype w P P' β β') ∘
      MeasurableEquiv.piCongrLeft (fun _ : κ => E) e) x
      ∂Measure.pi (fun _ : Fin (Fintype.card κ) => μ)) = _
    rw [hcomp, h.2]
    simp only [e.prod_comp]
end
def finiteOrthantCutoff  (A : ℝ) (s : Fin q → ℝ) : ℝ :=
  if ∑ j, s j ≤ A then Real.exp (∑ j, s j) else 0
def orthantSumCutoff  [Fintype ι] (A : ℝ) (z : ℝ × (ι → ℝ)) : ℝ :=
  if z.1 + ∑ j, z.2 j ≤ A then Real.exp (z.1 + ∑ j, z.2 j) else 0
theorem finite_orthant_cutoff_integrable   (hA : 0 ≤ A) :
    Integrable (finiteOrthantCutoff A : (Fin q → ℝ) → ℝ) (exponentialOrthantMeasure (Fin q)) := by
  have hm : Measurable (finiteOrthantCutoff A : (Fin q → ℝ) → ℝ) := by
    exact Measurable.ite (measurableSet_le (Finset.measurable_sum _ fun j _ => measurable_pi_apply j) measurable_const)
      (Real.measurable_exp.comp (Finset.measurable_sum _ fun j _ => measurable_pi_apply j)) measurable_const
  apply (orthant_cube_indicator_integrable A (Real.exp A)).mono' hm.aestronglyMeasurable
  rw [exponential_orthant_measure_eq_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Ici (0 : Fin q → ℝ)))] with s hs
  unfold finiteOrthantCutoff
  by_cases hsum : ∑ j, s j ≤ A
  · rw [ite_eq_left hsum, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
    have hcube : s ∈ Icc (0 : Fin q → ℝ) (fun _ => A) := by
      refine ⟨hs, ?_⟩
      intro j
      exact (Finset.single_le_sum (fun l _ => hs l) (Finset.mem_univ j)).trans hsum
    rw [Set.indicator_of_mem hcube]
    exact Real.exp_le_exp.mpr hsum
  · rw [ite_eq_right hsum, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) _
theorem orthant_cutoff_pair_integrable   (hA : 0 ≤ A) :
    Integrable (orthantSumCutoff A : (ℝ × (Fin m → ℝ)) → ℝ)
      ((volume.restrict (Ici ↑0)).prod (exponentialOrthantMeasure (Fin m))) := by
  have hp := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => volume.restrict (Ici (0 : ℝ))) 0).symm
  have h := (hp.integrable_comp_emb (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm.measurableEmbedding).mpr
    (finite_orthant_cutoff_integrable (q := m + 1) hA)
  convert h using 1
  · funext z
    simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
      finiteOrthantCutoff, orthantSumCutoff, Fin.sum_univ_succ, Fin.insertNth_zero,
      Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
  · rfl
def logScaleCutoff  [Fintype ι] (A : ℝ) (t : ι → ℝ) : ℝ :=
  if ∑ j, Real.log (1 + t j) ≤ A then 1 else 0
theorem log_scale_cutoff_change_pointwise {ι : Type*} [Fintype ι] (A : ℝ) (s : ι → ℝ) :
    (∏ j, Real.exp (s j)) * logScaleCutoff A (exponentialScaleMap s) =
      if ∑ j, s j ≤ A then Real.exp (∑ j, s j) else 0 := by
  classical
  have he : ∀ j, 1 + exponentialScaleMap s j = Real.exp (s j) := by
    intro j
    unfold exponentialScaleMap
    ring
  unfold logScaleCutoff
  simp_rw [he, Real.log_exp]
  split_ifs
  · rw [mul_one, ← Real.exp_sum]
  · exact mul_zero _
theorem finite_log_scale_cutoff_integral  (A : ℝ) :
    (∫ t : Fin q → ℝ in Ici 0, logScaleCutoff A t) =
      ∫ s : Fin q → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure (Fin q) := by
  rw [integral_exponential_scale_change, exponential_orthant_measure_eq_restrict]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => log_scale_cutoff_change_pointwise A s
theorem log_scale_cutoff_integral_reindex  [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (A ) :
    (∫ t : ι → ℝ in Ici 0, logScaleCutoff A t) =
      ∫ s : κ → ℝ in Ici 0, logScaleCutoff A s := by
  classical
  rw [← exponential_orthant_measure_eq_restrict, ← exponential_orthant_measure_eq_restrict]
  unfold exponentialOrthantMeasure
  have hp := measurePreserving_piCongrLeft (fun _ : ι => volume.restrict (Ici (0 : ℝ))) e
  rw [← hp.integral_comp']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => by
    have hs := e.sum_comp (fun j => Real.log (1 + ((MeasurableEquiv.piCongrLeft (fun _ => ℝ) e) s) j))
    simp only [MeasurableEquiv.piCongrLeft_apply_apply] at hs
    unfold logScaleCutoff
    dsimp only
    rw [← hs]
theorem log_scale_cutoff_integral_le_of_card  [Fintype ι]
     (hcard : Fintype.card ι = m + 1)  (hA : 0 ≤ A) :
    (∫ t : ι → ℝ in Ici 0, logScaleCutoff A t) ≤ Real.exp A * A ^ m := by
  rw [log_scale_cutoff_integral_reindex (Fintype.equivFinOfCardEq hcard).symm,
    finite_log_scale_cutoff_integral]
  have h_finite_orthant_cutoff_integral_le : (∫ s : Fin (m + 1) → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure (Fin (m + 1))) ≤
      Real.exp A * A ^ m := by
    have h_orthant_cutoff_split_integral : (∫ s : Fin (m + 1) → ℝ, finiteOrthantCutoff A s ∂exponentialOrthantMeasure (Fin (m + 1))) =
        ∫ z : ℝ × (Fin m → ℝ), orthantSumCutoff A z
        ∂((volume.restrict (Ici 0)).prod (exponentialOrthantMeasure (Fin m))) := by
      unfold exponentialOrthantMeasure
      rw [← ((measurePreserving_piFinSuccAbove
        (fun _ => volume.restrict (Ici 0)) 0).symm).integral_comp']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          finiteOrthantCutoff, orthantSumCutoff, Fin.sum_univ_succ, Fin.insertNth_zero,
          Equiv.coe_fn_mk, Fin.cons_succ, Fin.zero_succAbove, cast_eq, Fin.cons_zero]
    rw [h_orthant_cutoff_split_integral, integral_prod_symm _ (orthant_cutoff_pair_integrable hA)]
    have hdom : (fun s => ∫ v : ℝ in Ici 0, orthantSumCutoff A (v, s)) ≤ᵐ[
        exponentialOrthantMeasure (Fin m)]
        (Icc (0 : Fin m → ℝ) (fun _ => A)).indicator (fun _ => Real.exp A) := by
      rw [exponential_orthant_measure_eq_restrict]
      filter_upwards [ae_restrict_mem (measurableSet_Ici : MeasurableSet (Ici (0 : Fin m → ℝ)))] with s hs
      change (∫ v : ℝ in Ici 0, if v + ∑ j, s j ≤ A then Real.exp (v + ∑ j, s j) else 0) ≤ _
      have h_orthant_cutoff_scalar_integral S : (∫ v : ℝ in Ici 0, if v + S ≤ A then Real.exp (v + S) else 0) =
        if S ≤ A then Real.exp A - Real.exp S else 0 := by
        have he : (fun v => if v + S ≤ A then Real.exp (v + S) else 0) =
            (Iic (A - S)).indicator (fun v => Real.exp (v + S)) := by
          funext v
          have hh : v + S ≤ A ↔ v ≤ A - S := by constructor <;> intro h <;> linarith
          simp only [Set.indicator, mem_Iic, hh]
        rw [he, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
        have hs : Iic (A - S) ∩ Ici 0 = Icc 0 (A - S) := by ext v; simp only [mem_inter_iff, mem_Iic, mem_Ici, mem_Icc]; tauto
        rw [hs]
        by_cases h : S ≤ A
        · rw [ite_eq_left h]
          have hn : 0 ≤ A - S := by linarith
          have hf : (fun v => Real.exp (v + S)) = fun v => Real.exp S * Real.exp v := by
            funext v
            rw [Real.exp_add]
            ring
          rw [hf, integral_const_mul, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hn, integral_exp, Real.exp_zero, mul_sub, ← Real.exp_add, mul_one, show S + (A - S) = A by ring]
        · rw [ite_eq_right h, Icc_eq_empty_of_lt (by linarith)]
          simp
      rw [h_orthant_cutoff_scalar_integral]
      by_cases hcube : s ∈ Icc (0 : Fin m → ℝ) (fun _ => A)
      · rw [Set.indicator_of_mem hcube]
        split_ifs
        · linarith [Real.exp_nonneg (∑ j, s j)]
        · exact Real.exp_nonneg _
      · have hsum : ¬ ∑ j, s j ≤ A := by
          intro hsum
          apply hcube
          refine ⟨hs, ?_⟩
          intro j
          exact (Finset.single_le_sum (fun l _ => hs l) (Finset.mem_univ j)).trans hsum
        rw [ite_eq_right hsum, Set.indicator_of_notMem hcube]
    have h := integral_mono_ae (orthant_cutoff_pair_integrable hA).integral_prod_right
      (orthant_cube_indicator_integrable A (Real.exp A)) hdom
    rw [orthant_cube_indicator_integral hA] at h
    simpa only [Fintype.card_fin, mul_comm] using h
  exact h_finite_orthant_cutoff_integral_le
theorem spatial_cardinal_polynomial_scale_product  (i : Fin n) (U : Fin n → Covariate d) :
    spatialCardinalPolynomial U i = ∏ j : SpatialScaleIndex i, spatialCardinalAffine (U i) (U j.val) := by
  unfold spatialCardinalPolynomial
  rw [Finset.prod_subtype (p := fun j => j ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
    (fun j => by simp) (fun j => spatialCardinalAffine (U i) (U j))]
theorem spatial_cardinal_scale_product  (i : Fin n) (lam : ℝ)
    (U : Fin n → Covariate d) (t : SpatialScaleVector i) :
    spatialCardinalScale lam (spatialScaleExtend i t) U i =
      ∏ j : SpatialScaleIndex i, t j * lam ^ 2 *
        Real.exp (-t j * lam * spatialSquaredDistance (U i) (U j.val)) := by
  unfold spatialCardinalScale
  rw [Finset.prod_subtype (p := fun j : Fin n => j ≠ i) ((Finset.univ : Finset (Fin n)).erase i)
    (fun j => by simp) (fun j : Fin n => spatialScaleExtend i t j * lam ^ 2 *
      Real.exp (-spatialScaleExtend i t j * lam * spatialSquaredDistance (U i) (U j)))]
  apply Finset.prod_congr rfl
  intro j _
  simp only [spatialScaleExtend, dite_eq_left j.property]
theorem gaussian_tensor_cardinal_moments  [Fintype κ] 
    (lam ) (hlam : 0 ≤ lam) (t ) (ht : ∀ j, 0 ≤ t j)
    (x y β β') :
    Integrable (fun e => gaussianTensorObservable lam t x y e *
      gaussianTensorAmplitude lam e β β') (gaussianTensorMeasure κ d) ∧
      (∫ e, gaussianTensorObservable lam t x y e * gaussianTensorAmplitude lam e β β'
        ∂gaussianTensorMeasure κ d) =
        (∏ j, t j * lam ^ 2 * Real.exp (-t j * lam * spatialSquaredDistance (x j) (y j))) *
          (∏ j, spatialCardinalAffine (x j) (y j)).coeff β *
          (∏ j, spatialCardinalAffine (x j) (y j)).coeff β' := by
  let w := fun (j : κ) (e : GaussianPrimitiveMark d) =>
    gaussianPrimitiveLeft lam (t j) e (x j) * gaussianPrimitiveRight lam (t j) e (y j) *
      gaussianPrimitiveScalar d lam e
  let P := fun (_j : κ) (e : GaussianPrimitiveMark d) => gaussianAffinePolynomial e.2.1.1 e.2.2.1.1
  let P' := fun (_j : κ) (e : GaussianPrimitiveMark d) => gaussianAffinePolynomial e.2.1.2 e.2.2.1.2
  let p := fun j => spatialCardinalAffine (x j) (y j)
  let a := fun j => t j * lam ^ 2 * Real.exp (-t j * lam * spatialSquaredDistance (x j) (y j))
  have hpair (j : κ) (b b' : Fin d →₀ ℕ) :
      polynomialPairMoment (w j) (P j) (P' j) b b' =
        fun e => gaussianPrimitiveLeft lam (t j) e (x j) * gaussianPrimitiveRight lam (t j) e (y j) *
          gaussianPrimitiveAmplitude lam e b b' := by
    funext e
    dsimp [w, P, P', polynomialPairMoment, gaussianPrimitiveAmplitude, gaussianPrimitiveScalar]
    ring
  have hi (j : κ) (b b' : Fin d →₀ ℕ) :
      Integrable (polynomialPairMoment (w j) (P j) (P' j) b b') (gaussianPrimitiveMeasure d) := by
    rw [hpair]
    exact gaussianPrimitive_observable_integrable lam (t j) (x j) (y j) b b'
  have he (j : κ) (b b' : Fin d →₀ ℕ) :
      (∫ e, polynomialPairMoment (w j) (P j) (P' j) b b' e ∂gaussianPrimitiveMeasure d) =
        a j * (p j).coeff b * (p j).coeff b' := by
    rw [hpair]
    exact (gaussianPrimitive_separated_exact lam (t j) hlam (ht j) (x j) (y j) b b').symm
  have h := tensorPolynomialPairMoment_fintype_integral (gaussianPrimitiveMeasure d)
    w P P' p p a hi he β β'
  have hfun : tensorPolynomialPairMoment_fintype w P P' β β' =
      fun e => gaussianTensorObservable lam t x y e *
        gaussianTensorAmplitude lam e β β' := by
    funext e
    unfold tensorPolynomialPairMoment_fintype gaussianTensorObservable gaussianTensorAmplitude
      gaussianTensorScalar gaussianTensorLeftPolynomial gaussianTensorRightPolynomial gaussianPolynomialProduct
    dsimp [w, P, P']
    rw [Finset.prod_mul_distrib]
    ring
  rw [hfun] at h
  exact h
abbrev CenteredCardinalMark (d n : ℕ) (i : Fin n) :=
  SpatialScaleVector i × GaussianTensorMark (SpatialScaleIndex i) d
def centeredCardinalMeasure  (i d) (T : ℝ) :
    Measure (CenteredCardinalMark d n i) :=
  (spatialScaleMeasure i T).prod (gaussianTensorMeasure (SpatialScaleIndex i) d)
def centeredCardinalAmplitude  (i ) (lam : ℝ)
    (z : CenteredCardinalMark d n i) : HighFrameIndex d D → HighFrameIndex d D → ℝ :=
  gaussianTensorSymmetricAmplitude lam z.2
def centeredCardinalFactor  (i ) (lam : ℝ)
    (z : CenteredCardinalMark d n i) (l : Fin n) (x : Covariate d) : ℝ :=
  if h : l ≠ i then gaussianPrimitiveRight lam (z.1 ⟨l, h⟩) (z.2 ⟨l, h⟩) x
    else ∏ j : SpatialScaleIndex i, gaussianPrimitiveLeft lam (z.1 j) (z.2 j) x
theorem centered_cardinal_factor_abs_le_one  (i : Fin n) (lam : ℝ)
    (z : CenteredCardinalMark d n i) (l : Fin n) (x : Covariate d) (hx : ∀ r, |x r| ≤ 2) :
    |centeredCardinalFactor i lam z l x| ≤ 1 := by
  unfold centeredCardinalFactor
  split_ifs
  have h_gaussianPrimitiveRight_bound t (e : GaussianPrimitiveMark d) : |gaussianPrimitiveRight lam t e x| ≤ 1 := by
    unfold gaussianPrimitiveRight
    rw [abs_mul, abs_mul]
    exact (mul_le_mul (mul_le_mul (gaussianTrig_abs_le_one lam t e.1 x e.2.2.2) (gaussianAffineFactor_abs_le_one e.2.1.1 e.2.2.1.1 x (hx _)) (abs_nonneg _) (by norm_num)) (gaussianAffineFactor_abs_le_one e.2.1.2 e.2.2.1.2 x (hx _))
      (abs_nonneg _) (by norm_num)).trans_eq (by ring)
  · exact h_gaussianPrimitiveRight_bound _ _
  · rw [Finset.abs_prod]
    have h_gaussianPrimitiveLeft_bound t (e : GaussianPrimitiveMark d) : |gaussianPrimitiveLeft lam t e x| ≤ 1 := gaussianTrig_abs_le_one _ _ _ _ _
    calc
      _ ≤ ∏ _j : SpatialScaleIndex i, 1 :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => (h_gaussianPrimitiveLeft_bound _ _))
      _ = _ := by simp
theorem centered_cardinal_factor_measurable  (i : Fin n) (lam : ℝ)
    (l : Fin n) (x : Covariate d) :
    Measurable (fun z : CenteredCardinalMark d n i => centeredCardinalFactor i lam z l x) := by
  unfold centeredCardinalFactor
  split_ifs with h
  · have hm : Measurable (fun z : CenteredCardinalMark d n i => (z.1 ⟨l, h⟩, z.2 ⟨l, h⟩)) :=
      ((measurable_pi_apply (⟨l, h⟩ : SpatialScaleIndex i)).comp measurable_fst).prodMk
        ((measurable_pi_apply (⟨l, h⟩ : SpatialScaleIndex i)).comp measurable_snd)
    have h_gaussianPrimitiveRight_scale_measurable : Measurable (fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveRight lam z.1 z.2 x) := by
      have hm : Measurable (fun z : (ℝ × Covariate d) × GaussianPrimitiveIndex d =>
          gaussianPrimitiveRight lam z.1.1 (z.1.2, z.2) x) := by
        apply measurable_from_prod_countable_left
        intro h
        change Measurable (fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 x h.2.2 *
          gaussianAffineFactor h.1.1 h.2.1.1 x * gaussianAffineFactor h.1.2 h.2.1.2 x)
        have ht : Measurable (fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 x h.2.2) := by
          cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
            unfold gaussianPhase <;> fun_prop
        exact (ht.mul_const _).mul_const _
      exact hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
    have hh := h_gaussianPrimitiveRight_scale_measurable.comp hm
    change Measurable (fun z : CenteredCardinalMark d n i =>
      gaussianPrimitiveRight lam (z.1 ⟨l, h⟩) (z.2 ⟨l, h⟩) x) at hh
    exact hh
  · apply Finset.measurable_fun_prod
    intro j _
    have hm : Measurable (fun z : CenteredCardinalMark d n i => (z.1 j, z.2 j)) :=
      (((measurable_pi_apply j).comp measurable_fst).prodMk
        ((measurable_pi_apply j).comp measurable_snd))
    have h_gaussianPrimitiveLeft_scale_measurable : Measurable (fun z : ℝ × GaussianPrimitiveMark d => gaussianPrimitiveLeft lam z.1 z.2 x) := by
      have hm : Measurable (fun z : (ℝ × Covariate d) × GaussianPrimitiveIndex d =>
          gaussianPrimitiveLeft lam z.1.1 (z.1.2, z.2) x) := by
        apply measurable_from_prod_countable_left
        intro h
        change Measurable (fun z : ℝ × Covariate d => gaussianTrig lam z.1 z.2 x h.2.2)
        cases h.2.2 <;> simp only [gaussianTrig, Bool.false_eq_true, ite_false, ite_true] <;>
          unfold gaussianPhase <;> fun_prop
      exact hm.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
        (measurable_snd.comp measurable_snd))
    have hh := h_gaussianPrimitiveLeft_scale_measurable.comp hm
    change Measurable (fun z : CenteredCardinalMark d n i =>
      gaussianPrimitiveLeft lam (z.1 j) (z.2 j) x) at hh
    exact hh
theorem centered_cardinal_amplitude_measurable  (i : Fin n) (lam : ℝ)
    (β β' : HighFrameIndex d D) :
    Measurable (fun z : CenteredCardinalMark d n i => centeredCardinalAmplitude i lam z β β') :=
  (gaussianTensorSymmetricAmplitude_measurable lam β β').comp measurable_snd
theorem centered_cardinal_measure_finite  (i : Fin n) (d : ℕ)  (hT : 1 ≤ T) :
    IsFiniteMeasure (centeredCardinalMeasure i d T) := by
  letI := spatial_scale_measure_finite i T hT
  letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
  unfold centeredCardinalMeasure
  infer_instance
theorem centered_cardinal_cost_integrable  (i : Fin n) (lam : ℝ)
     (hT : 1 ≤ T) :
    Integrable (separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam))
      (centeredCardinalMeasure i d T) := by
  letI := spatial_scale_measure_finite i T hT
  letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
  have h := (integrable_const ↑1 (μ := spatialScaleMeasure i T)).mul_prod
    (gaussianTensorSymmetricAmplitude_cost_integrable (κ := SpatialScaleIndex i) (d := d) (D := D) lam)
  change Integrable (fun z : CenteredCardinalMark d n i =>
    separatedMatrixCost (gaussianTensorSymmetricAmplitude lam) z.2)
      ((spatialScaleMeasure i T).prod (gaussianTensorMeasure (SpatialScaleIndex i) d))
  simpa only [one_mul] using h
theorem centered_cardinal_cost_integral_le  (hn : 2 ≤ n) (i : Fin n) (lam : ℝ)
     (hT : 1 ≤ T) :
    (∫ z, separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam) z ∂centeredCardinalMeasure i d T) ≤
      (1024 * |lam| * ↑d ^ 2) ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
  have h_centered_cardinal_cost_integral_eq : (∫ z, separatedMatrixCost (centeredCardinalAmplitude (D := D) i lam) z ∂centeredCardinalMeasure i d T) =
      (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) *
        (∫ e, separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := SpatialScaleIndex i)
          (d := d) (D := D) lam) e ∂gaussianTensorMeasure (SpatialScaleIndex i) d) := by
    letI := gaussianTensorMeasure_finite (SpatialScaleIndex i) d
    letI : SFinite (spatialScaleMeasure i T) := by unfold spatialScaleMeasure; infer_instance
    have h := integral_prod_mul (μ := spatialScaleMeasure i T)
      (ν := gaussianTensorMeasure (SpatialScaleIndex i) d) (fun _ => ↑1)
      (separatedMatrixCost (gaussianTensorSymmetricAmplitude (κ := SpatialScaleIndex i) (d := d) (D := D) lam))
    simp only [one_mul, integral_const, smul_eq_mul, mul_one] at h
    simpa only [centeredCardinalMeasure, centeredCardinalAmplitude, separatedMatrixCost,
      spatialScaleMeasure, Measure.real, Measure.restrict_apply_univ] using h
  rw [h_centered_cardinal_cost_integral_eq]
  have hcost := gaussianTensorSymmetricAmplitude_integrated_cost
    (κ := SpatialScaleIndex i) (d := d) (D := D) lam
  rw [spatial_scale_index_card] at hcost
  have h_spatial_scale_domain_volume_le_uniform : (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) ≤
      2 ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2) := by
    have hlog  := Real.log_nonneg hT
    have h := pow_le_pow_left₀ hlog (by linarith : Real.log T ≤ 1 + Real.log T) (n - 2)
    have ht := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : n - 2 ≤ n - 1)
    have hh := mul_le_mul h ht (by positivity : 0 ≤ (2 : ℝ) ^ (n - 2))
      (by positivity : 0 ≤ (1 + Real.log T) ^ (n - 2))
    have hhh := mul_le_mul_of_nonneg_right hh (sq_nonneg T)
    have h_spatial_scale_domain_volume_le : (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) ≤
        T ^ 2 * (2 * Real.log T) ^ (n - 2) := by
      have hcard : Fintype.card (SpatialScaleIndex i) = n - 2 + 1 := by
        rw [spatial_scale_index_card]
        omega
      have h_spatial_scale_domain_volume_eq_cutoff : (volume : Measure (SpatialScaleVector i)).real (spatialScaleDomain i T) =
          ∫ t : SpatialScaleVector i in Ici 0, logScaleCutoff (2 * Real.log T) t := by
        have hlog : Measurable (fun t : SpatialScaleVector i => ∑ j, Real.log (1 + t j)) :=
          Finset.measurable_sum _ fun j _ => Real.measurable_log.comp
            (measurable_const.add (measurable_pi_apply j))
        have hm : MeasurableSet {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T} :=
          measurableSet_le hlog measurable_const
        have he : (logScaleCutoff (2 * Real.log T) : SpatialScaleVector i → ℝ) =
            {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T}.indicator (fun _ => 1) := by
          funext t
          simp only [logScaleCutoff, Set.indicator, mem_setOf_eq]
        rw [he, integral_indicator hm, Measure.restrict_restrict hm]
        have h_spatial_scale_domain_original : spatialScaleDomain i T = Ici 0 ∩
            {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T} := by
          ext t
          have he (ht : t ∈ Ici (0 : SpatialScaleVector i)) :
              spatialScaleLogSum i t = ∑ j, Real.log (1 + t j) := by
            apply Finset.sum_congr rfl
            intro j _
            have htj : ↑0 ≤ t j := ht j
            rw [max_eq_right htj]
          constructor
          · rintro ⟨ht, hlog⟩
            refine ⟨ht, ?_⟩
            change spatialScaleLogSum i t ≤ 2 * Real.log T at hlog
            rw [he ht] at hlog
            exact hlog
          · rintro ⟨ht, hlog⟩
            refine ⟨ht, ?_⟩
            change spatialScaleLogSum i t ≤ 2 * Real.log T
            rw [he ht]
            exact hlog
        have hs : {t : SpatialScaleVector i | ∑ j, Real.log (1 + t j) ≤ 2 * Real.log T} ∩ Ici 0 =
            spatialScaleDomain i T := by rw [h_spatial_scale_domain_original, Set.inter_comm]
        rw [hs, integral_const]
        simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one]
      rw [h_spatial_scale_domain_volume_eq_cutoff]
      have h := log_scale_cutoff_integral_le_of_card hcard
        (by linarith [Real.log_nonneg hT] : 0 ≤ 2 * Real.log T)
      have he : Real.exp (2 * Real.log T) = T ^ 2 := by
        have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
        simpa only [Nat.cast_ofNat, Real.exp_log hTpos] using Real.exp_nat_mul (Real.log T) 2
      rw [he] at h
      exact h
    calc
      _ ≤ _ := h_spatial_scale_domain_volume_le
      _ ≤ _ := by rw [mul_pow]; nlinarith [hhh]
  have := Real.log_nonneg hT
  have h := mul_le_mul (h_spatial_scale_domain_volume_le_uniform) hcost (integral_nonneg (fun e => Finset.sum_nonneg (fun β _ => Finset.sum_nonneg (fun β' _ => abs_nonneg _)))) (by positivity :
    0 ≤ 2 ^ (n - 1) * T ^ 2 * (1 + Real.log T) ^ (n - 2))
  convert h using 1
  rw [show (1024 * |lam| * d ^ 2) = 2 * (512 * |lam| * d ^ 2) by ring, mul_pow]
  ring
theorem centered_cardinal_symmetric_tensor_exact  (i : Fin n) (lam : ℝ) (hlam : 0 ≤ lam)
    (t : SpatialScaleVector i) (ht : t ∈ Ici 0) (U : Fin n → Covariate d) (β β' : HighFrameIndex d D) :
    (∫ e : GaussianTensorMark (SpatialScaleIndex i) d,
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorSymmetricAmplitude lam e β β' ∂gaussianTensorMeasure (SpatialScaleIndex i) d) =
      spatialCenteredCardinalMatrix i lam U t β β' := by
  have h_centered_cardinal_raw_tensor_integrable (β : HighFrameIndex d D) (β' : HighFrameIndex d D) : Integrable (fun e : GaussianTensorMark (SpatialScaleIndex i) d =>
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β β') (gaussianTensorMeasure (SpatialScaleIndex i) d) := (gaussian_tensor_cardinal_moments lam hlam t (fun j => ht j)
    (fun _ => U i) (fun j => U j.val) _ _).1
  have h_centered_cardinal_raw_tensor_exact (β : HighFrameIndex d D) (β' : HighFrameIndex d D) : (∫ e : GaussianTensorMark (SpatialScaleIndex i) d,
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β β' ∂gaussianTensorMeasure (SpatialScaleIndex i) d) =
      spatialCenteredCardinalMatrix i lam U t β β' := by
    have h := (gaussian_tensor_cardinal_moments lam hlam t (fun j => ht j)
      (fun _ => U i) (fun j => U j.val) (polynomialBoxExponent β.val) (polynomialBoxExponent β'.val)).2
    simpa only [gaussianTensorFrameAmplitude, gaussianTensorAmplitude, spatialCenteredCardinalMatrix, highFrameCoefficients,
      spatial_cardinal_scale_product, spatial_cardinal_polynomial_scale_product] using h
  have he : (fun e : GaussianTensorMark (SpatialScaleIndex i) d =>
      gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorSymmetricAmplitude lam e β β') =
      fun e => (gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β β' +
        gaussianTensorObservable lam t (fun _ => U i) (fun j => U j.val) e *
        gaussianTensorFrameAmplitude lam e β' β) / 2 := by
    funext e
    unfold gaussianTensorSymmetricAmplitude realMatrixSymmetrize
    ring
  rw [he, integral_div, integral_add
    (h_centered_cardinal_raw_tensor_integrable β β')
    (h_centered_cardinal_raw_tensor_integrable β' β),
    h_centered_cardinal_raw_tensor_exact β β',
    h_centered_cardinal_raw_tensor_exact β' β]
  unfold spatialCenteredCardinalMatrix
  ring
theorem centered_cardinal_product_entry_integrable  (i : Fin n) (lam : ℝ)
     (hT : 1 ≤ T) (U : Fin n → Covariate d) (hU : ∀ l r, |U l r| ≤ 2)
    (β β' : HighFrameIndex d D) :
    Integrable (fun z => (∏ l, centeredCardinalFactor i lam z l (U l)) *
      centeredCardinalAmplitude i lam z β β') (centeredCardinalMeasure i d T) := by
  have hb : ∀ z : CenteredCardinalMark d n i, |∏ l, centeredCardinalFactor i lam z l (U l)| ≤ 1 := by
    intro z
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _l : Fin n, (1 : ℝ) := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _)
        (fun l _ => centered_cardinal_factor_abs_le_one i lam z l (U l) (hU l))
      _ = _ := by simp
  have h_centered_cardinal_entry_integrable  := separatedMatrix_entry_integrable _ _ (centered_cardinal_amplitude_measurable i lam)
    (centered_cardinal_cost_integrable i lam hT) β β'
  have h := h_centered_cardinal_entry_integrable.mul_bdd (Finset.measurable_fun_prod _ (fun l _ => centered_cardinal_factor_measurable i lam l (U l))).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => by rw [Real.norm_eq_abs]; exact hb z))
  exact h.congr (Filter.Eventually.of_forall (fun z => mul_comm _ _))
end NearlyMinimax
