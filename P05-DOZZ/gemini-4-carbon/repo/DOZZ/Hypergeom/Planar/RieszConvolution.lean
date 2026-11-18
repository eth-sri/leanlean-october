/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import DOZZ.Hypergeom.Planar.Beta
public import DOZZ.Hypergeom.Planar.TwoPointRpow

/-! Gaussian and Laplace foundations for the positive planar Riesz convolution. -/

@[expose] public section

open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal

namespace DOZZ.Proofs





/-- The positive planar Riesz kernel is integrable exactly in the range needed below. -/
theorem positive_riesz_convolution_integrable (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (z : ℂ) (hz : z ≠ 0) :
    Integrable (fun u : ℂ => ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) volume := by
  rw [integrableOn_two_point_rpow_iff (-β) (k - 2) z hz]
  exact ⟨by linarith, by linarith, by linarith⟩

/-- Positive Riesz convolution on the plane, evaluated by Laplace, Gaussian, and beta integrals.
The variables are the source exponents: `|u|^(-β) |u-z|^(k-2)`. -/
theorem positive_riesz_convolution_integral (k β : ℝ) (hk : 0 < k)
    (hβ : k < β) (hβ₂ : β < 2) (z : ℂ) (hz : z ≠ 0) :
    (∫ u : ℂ, ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) =
      Real.pi * (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
        Real.Gamma ((β - k) / 2) /
          (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
            Real.Gamma (1 + (k - β) / 2))) * ‖z‖ ^ (k - β) := by
  have positive_riesz_lintegral_formula {a b : ℝ} {z : ℂ} (ha : 0 < a) (ha' : a < 1) (hb : 0 < b) (hb' : b < 1) (hab : 1 < a + b) (hz : z ≠ 0) : (∫⁻ u : ℂ, ENNReal.ofReal (‖u‖ ^ (-2 * a) * ‖u - z‖ ^ (-2 * b))) =
        ENNReal.ofReal (Real.pi * (Real.Gamma (a + b - 1) * ‖z‖ ^ (-2 * (a + b - 1)) *
          (Real.Gamma (1 - a) * Real.Gamma (1 - b) /
            (Real.Gamma a * Real.Gamma b * Real.Gamma (2 - a - b))))) := by
    have lintegral_beta_tail {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : (∫⁻ v : ℝ in Ioi 0, ENNReal.ofReal (v ^ (x - 1) * (1 + v) ^ (-(x + y)))) =
          ENNReal.ofReal (Real.Gamma x * Real.Gamma y / Real.Gamma (x + y)) := by
      let f : ℝ → ℝ := fun v => v / (1 + v)
      have hImg : f '' Ioi 0 = Ioo 0 1 := by
        ext t; constructor
        · rintro ⟨v, hv : 0 < v, rfl⟩
          exact ⟨div_pos hv (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩
        · rintro ⟨ht, ht1⟩
          exact ⟨t / (1 - t), div_pos ht (sub_pos.2 ht1), by dsimp [f]; field_simp; ring⟩
      have hInj : InjOn f (Ioi 0) := fun v (hv : 0 < v) w (hw : 0 < w) h => by
        nlinarith [(div_eq_div_iff (by linarith : 1 + v ≠ 0) (by linarith : 1 + w ≠ 0)).1 h]
      have hder : ∀ v ∈ Ioi (0 : ℝ), HasDerivWithinAt f ((1 + v) ^ 2)⁻¹ (Ioi 0) v := fun v (hv : 0 < v) =>
        ((((hasDerivAt_id v).div ((hasDerivAt_id v).const_add 1) (by dsimp; linarith)).congr_deriv
          (by dsimp; field_simp [show 1 + v ≠ 0 by linarith]; ring)).hasDerivWithinAt)
      have hchg := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hInj
        (fun t : ℝ => t ^ (x - 1) * (1 - t) ^ (y - 1))
      rw [hImg, setIntegral_congr_set Ioo_ae_eq_Ioc] at hchg
      have hval : (∫ v : ℝ in Ioi 0, v ^ (x - 1) * (1 + v) ^ (-(x + y))) =
          Real.Gamma x * Real.Gamma y / Real.Gamma (x + y) := by
        have h1 : (∫ v : ℝ in Ioi 0, v ^ (x - 1) * (1 + v) ^ (-(x + y))) =
            ∫ t : ℝ in Ioc 0 1, t ^ (x - 1) * (1 - t) ^ (y - 1) := by
          refine (setIntegral_congr_fun measurableSet_Ioi fun v (hv : 0 < v) => ?_).trans hchg.symm
          have hd : 0 < 1 + v := by linarith
          dsimp only [smul_eq_mul, f]
          rw [show 1 - v / (1 + v) = 1 / (1 + v) by field_simp; ring, abs_of_pos (by positivity),
            ← Real.rpow_natCast (1 + v) 2, Real.div_rpow hv.le hd.le, Real.div_rpow zero_le_one hd.le,
            Real.one_rpow, Real.rpow_neg hd.le]
          have hp : (1 + v) ^ (2 : ℝ) * (1 + v) ^ (x - 1) * (1 + v) ^ (y - 1) = (1 + v) ^ (x + y) := by
            rw [← Real.rpow_add hd, ← Real.rpow_add hd]; congr 1; ring
          field_simp [(Real.rpow_pos_of_pos hd _).ne']; rw [← hp]; ring
        have hbetaC := Complex.betaIntegral_eq_Gamma_mul_div (x : ℂ) (y : ℂ)
          (by simpa using hx) (by simpa using hy)
        rw [betaIntegral_ofReal, ← Complex.ofReal_add, Complex.Gamma_ofReal,
          Complex.Gamma_ofReal, Complex.Gamma_ofReal] at hbetaC
        exact h1.trans (Complex.ofReal_injective (by simpa using hbetaC))
      have hInt : IntegrableOn (fun v : ℝ => v ^ (x - 1) * (1 + v) ^ (-(x + y))) (Ioi 0) := by
        by_contra hnot
        have hpos : 0 < Real.Gamma x * Real.Gamma y / Real.Gamma (x + y) :=
          div_pos (mul_pos (Real.Gamma_pos_of_pos hx) (Real.Gamma_pos_of_pos hy))
            (Real.Gamma_pos_of_pos (add_pos hx hy))
        linarith [hval.symm.trans (integral_undef hnot)]
      rw [← ofReal_integral_eq_lintegral_ofReal hInt
        (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with v (hv : 0 < v);
            exact mul_nonneg (Real.rpow_nonneg hv.le _) (Real.rpow_nonneg (by linarith) _)), hval]
    have lintegral_laplace_power {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t ^ (a - 1) * Real.exp (-(x * t)))) =
          ENNReal.ofReal (Real.Gamma a * x ^ (-a)) := by
      have hInt : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(x * t))) (Ioi 0) := by
        convert integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := x)
          (by linarith) one_pos hx using 1
        ext t; simp [neg_mul]
      rw [← ofReal_integral_eq_lintegral_ofReal hInt
          (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t); positivity),
        Real.integral_rpow_mul_exp_neg_mul_Ioi ha hx, one_div, Real.inv_rpow hx.le,
        Real.rpow_neg hx.le, mul_comm]
    have lintegral_planar_gaussian_product {s t : ℝ} (hs : 0 < s) (ht : 0 < t) (z : ℂ) : (∫⁻ u : ℂ, ENNReal.ofReal (Real.exp (-(‖u‖ ^ 2 * t)) * Real.exp (-(‖u - z‖ ^ 2 * s)))) =
          ENNReal.ofReal (Real.pi / (t + s) * Real.exp (-(t * s / (t + s)) * ‖z‖ ^ 2)) := by
      let q := t + s
      let c := s / q
      have hq : 0 < q := by dsimp [q]; linarith
      have hfun (u : ℂ) : Real.exp (-(‖u‖ ^ 2 * t)) * Real.exp (-(‖u - z‖ ^ 2 * s)) =
          Real.exp (-q * ‖u - c • z‖ ^ 2) * Real.exp (-(t * s / q) * ‖z‖ ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1
        rw [norm_sub_sq_real u z, norm_sub_sq_real u (c • z), real_inner_smul_right, norm_smul,
          Real.norm_eq_abs, abs_of_pos (div_pos hs hq)]
        dsimp [q, c]; field_simp; ring
      have hbase : Integrable (fun u : ℂ => Real.exp (-q * ‖u‖ ^ 2)) := by
        have hc : Integrable (fun u : ℂ => Complex.exp (-(q : ℂ) * ‖u‖ ^ 2)) := by
          simpa [Complex.ofReal_exp] using
            GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) (b := (q : ℂ)) (by simp [hq]) 0 (0 : ℂ)
        exact hc.re.congr (ae_of_all _ fun u => by
          dsimp only
          rw [show -(q : ℂ) * ‖u‖ ^ 2 = ((-q * ‖u‖ ^ 2 : ℝ) : ℂ) by push_cast; ring]
          exact Complex.exp_ofReal_re _)
      have hshift : Integrable (fun u : ℂ => Real.exp (-q * ‖u - c • z‖ ^ 2)) := by
        simpa [sub_eq_add_neg, add_comm] using hbase.comp_add_left (-(c • z))
      have hprod : Integrable (fun u : ℂ => Real.exp (-(‖u‖ ^ 2 * t)) * Real.exp (-(‖u - z‖ ^ 2 * s))) :=
        (hshift.mul_const _).congr (ae_of_all _ fun u => (hfun u).symm)
      rw [← ofReal_integral_eq_lintegral_ofReal hprod (ae_of_all _ fun _ => by positivity)]
      congr 1
      simp_rw [hfun, integral_mul_const]
      congr 1
      have hmp := (MeasureTheory.measurePreserving_add_right volume (c • z)).integral_comp
        (Homeomorph.addRight (c • z)).measurableEmbedding (fun u : ℂ => Real.exp (-q * ‖u - c • z‖ ^ 2))
      simp only [add_sub_cancel_right] at hmp
      simpa [Complex.finrank_real_complex] using
        hmp.symm.trans (GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) hq)
    let A : ℂ → ℝ → ℝ≥0∞ := fun u t => ENNReal.ofReal (t ^ (a - 1) * Real.exp (-(‖u‖ ^ 2 * t)))
    let B : ℂ → ℝ → ℝ≥0∞ := fun u s => ENNReal.ofReal (s ^ (b - 1) * Real.exp (-(‖u - z‖ ^ 2 * s)))
    let C := ENNReal.ofReal (Real.Gamma a) * ENNReal.ofReal (Real.Gamma b)
    let R := ‖z‖
    have hR : 0 < R := norm_pos_iff.2 hz
    let p := a + b - 1
    have hp : 0 < p := by dsimp [p]; linarith
    have hpow_mul {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
        (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t ^ (q - 1) * Real.exp (-(r ^ 2 * t)))) =
          ENNReal.ofReal (Real.Gamma q) * ENNReal.ofReal (r ^ (-2 * q)) := by
      rw [lintegral_laplace_power hq (by positivity), ← Real.rpow_natCast r 2,
        ← Real.rpow_mul hr.le, show ((2 : ℕ) : ℝ) * -q = -2 * q by push_cast; ring,
        ENNReal.ofReal_mul (Real.Gamma_pos_of_pos hq).le]
    have hpt : ∀ᵐ u : ℂ, C * ENNReal.ofReal (‖u‖ ^ (-2 * a) * ‖u - z‖ ^ (-2 * b)) =
        ∫⁻ t in Ioi 0, ∫⁻ s in Ioi 0, A u t * B u s := by
      filter_upwards [Measure.ae_ne volume (0 : ℂ), Measure.ae_ne volume z] with u hu0 huz
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg (norm_nonneg _) _),
        show C * (ENNReal.ofReal (‖u‖ ^ (-2 * a)) * ENNReal.ofReal (‖u - z‖ ^ (-2 * b))) =
          (ENNReal.ofReal (Real.Gamma a) * ENNReal.ofReal (‖u‖ ^ (-2 * a))) *
            (ENNReal.ofReal (Real.Gamma b) * ENNReal.ofReal (‖u - z‖ ^ (-2 * b))) by dsimp [C]; ring,
        ← hpow_mul ha (norm_pos_iff.2 hu0), ← hpow_mul hb (norm_pos_iff.2 (sub_ne_zero.2 huz)),
        lintegral_lintegral_mul (by fun_prop) (by fun_prop)]
    have hscaled : C * (∫⁻ u : ℂ, ENNReal.ofReal (‖u‖ ^ (-2 * a) * ‖u - z‖ ^ (-2 * b))) =
        ENNReal.ofReal Real.pi * ENNReal.ofReal (Real.Gamma p * R ^ (-2 * p) *
          (Real.Gamma (1 - a) * Real.Gamma (1 - b) / Real.Gamma (2 - a - b))) := by
      rw [← lintegral_const_mul C (by fun_prop), lintegral_congr_ae hpt,
        lintegral_lintegral_swap (by fun_prop)]
      have h1 : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ u : ℂ, ∫⁻ s in Ioi (0 : ℝ), A u t * B u s) =
          ENNReal.ofReal Real.pi * ∫⁻ t in Ioi (0 : ℝ), ∫⁻ s in Ioi (0 : ℝ),
            ENNReal.ofReal (t ^ (a - 1) * s ^ (b - 1) / (t + s) *
              Real.exp (-(t * s / (t + s) * R ^ 2))) := by
        rw [← lintegral_const_mul _ (by fun_prop)]
        refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) => ?_
        rw [lintegral_lintegral_swap (by fun_prop), ← lintegral_const_mul _ (by fun_prop)]
        refine setLIntegral_congr_fun measurableSet_Ioi fun s (hs : 0 < s) => ?_
        have hAB (u : ℂ) : A u t * B u s = ENNReal.ofReal (t ^ (a - 1) * s ^ (b - 1)) *
            ENNReal.ofReal (Real.exp (-(‖u‖ ^ 2 * t)) * Real.exp (-(‖u - z‖ ^ 2 * s))) := by
          dsimp [A, B]
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
          congr 1; ring
        simp_rw [hAB]
        rw [lintegral_const_mul _ (by fun_prop), lintegral_planar_gaussian_product hs ht z,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul Real.pi_pos.le]
        congr 1; dsimp [R]; ring
      rw [h1]; congr 1
      let G : ℝ → ℝ → ℝ≥0∞ := fun t s => ENNReal.ofReal
        (t ^ (a - 1) * s ^ (b - 1) / (t + s) * Real.exp (-(t * s / (t + s) * R ^ 2)))
      have hsc (t : ℝ) (ht : 0 < t) : (∫⁻ s in Ioi 0, G t s) =
          ∫⁻ y in Ioi 0, ENNReal.ofReal t * G t (t * y) := by
        have hm : MonotoneOn (fun y : ℝ => t * y) (Ioi 0) := fun _ _ _ _ h => mul_le_mul_of_nonneg_left h ht.le
        have hd : ∀ y ∈ Ioi (0 : ℝ), HasDerivWithinAt (fun y => t * y) t (Ioi 0) y := fun y _ => by
          simpa [mul_comm] using ((hasDerivAt_id y).const_mul t).hasDerivWithinAt
        have hc := MeasureTheory.lintegral_image_eq_lintegral_deriv_mul_of_monotoneOn
          measurableSet_Ioi hd hm (G t)
        rwa [show (fun y => t * y) '' Ioi 0 = Ioi 0 by
          ext s; constructor
          · rintro ⟨y, hy : 0 < y, rfl⟩; exact mul_pos ht hy
          · intro hs; exact ⟨s / t, div_pos hs ht, mul_div_cancel₀ _ ht.ne'⟩] at hc
      change (∫⁻ t in Ioi 0, ∫⁻ s in Ioi 0, G t s) = _
      rw [setLIntegral_congr_fun measurableSet_Ioi hsc, lintegral_lintegral_swap (by fun_prop)]
      have hy_step : (∫⁻ y in Ioi (0 : ℝ), ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal t * G t (t * y)) =
          ENNReal.ofReal (Real.Gamma p * R ^ (-2 * p)) *
            ∫⁻ y in Ioi (0 : ℝ), ENNReal.ofReal (y ^ ((1 - a) - 1) * (1 + y) ^ (-((1 - a) + (1 - b)))) := by
        rw [← lintegral_const_mul _ (by fun_prop)]
        refine setLIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
        have hd1 : 0 < 1 + y := by linarith
        have hGt : ∀ t ∈ Ioi (0 : ℝ), ENNReal.ofReal t * G t (t * y) =
            ENNReal.ofReal (y ^ (b - 1) / (1 + y)) *
              ENNReal.ofReal (t ^ (p - 1) * Real.exp (-((R ^ 2 * y / (1 + y)) * t))) := fun t (ht : 0 < t) => by
          dsimp [G]
          rw [← ENNReal.ofReal_mul ht.le, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [Real.mul_rpow ht.le hy.le, show p - 1 = (a - 1) + (b - 1) by dsimp [p]; ring,
            Real.rpow_add ht, show t + t * y = t * (1 + y) by ring]
          have : -(t * (t * y) / (t * (1 + y)) * R ^ 2) = -(R ^ 2 * y / (1 + y) * t) := by
            field_simp [ht.ne', hd1.ne']
          rw [this]; field_simp [ht.ne', hd1.ne']
        rw [setLIntegral_congr_fun measurableSet_Ioi hGt, lintegral_const_mul _ (by fun_prop),
          lintegral_laplace_power hp (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (mul_pos (Real.Gamma_pos_of_pos hp) (Real.rpow_pos_of_pos hR _)).le]
        congr 1
        rw [Real.div_rpow (by positivity) hd1.le, Real.mul_rpow (sq_nonneg R) hy.le,
          ← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le,
          show ((2 : ℕ) : ℝ) * -p = -2 * p by push_cast; ring,
          Real.rpow_neg hd1.le, div_inv_eq_mul]
        have hy_add : y ^ (b - 1) * y ^ (-p) = y ^ ((1 - a) - 1) := by
          rw [← Real.rpow_add hy]; congr 1; dsimp [p]; ring
        have hd_sub : (1 + y) ^ p / (1 + y) = (1 + y) ^ (-((1 - a) + (1 - b))) := by
          rw [← Real.rpow_sub_one hd1.ne']; congr 1; dsimp [p]; ring
        calc y ^ (b - 1) / (1 + y) * (Real.Gamma p * (R ^ (-2 * p) * y ^ (-p) * (1 + y) ^ p))
            = Real.Gamma p * R ^ (-2 * p) * ((y ^ (b - 1) * y ^ (-p)) * ((1 + y) ^ p / (1 + y))) := by ring
          _ = _ := by rw [hy_add, hd_sub]
      rw [hy_step, lintegral_beta_tail (by linarith : 0 < 1 - a) (by linarith : 0 < 1 - b),
        ← ENNReal.ofReal_mul (mul_pos (Real.Gamma_pos_of_pos hp) (Real.rpow_pos_of_pos hR _)).le]
      congr 2; ring
    have hCpos := mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos hb)
    have hCeq : C = ENNReal.ofReal (Real.Gamma a * Real.Gamma b) :=
      (ENNReal.ofReal_mul (Real.Gamma_pos_of_pos ha).le).symm
    have hC0 : C ≠ 0 := by rw [hCeq]; positivity
    have hCtop : C ≠ ∞ := by rw [hCeq]; exact ENNReal.ofReal_ne_top
    have h1a := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - a)
    have h1b := Real.Gamma_pos_of_pos (by linarith : 0 < 1 - b)
    have h2ab := Real.Gamma_pos_of_pos (by linarith : 0 < 2 - a - b)
    have hGp := Real.Gamma_pos_of_pos hp
    refine (ENNReal.mul_left_inj hC0 hCtop).1 ?_
    rw [mul_comm _ C, hscaled, hCeq, ← ENNReal.ofReal_mul Real.pi_pos.le,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; dsimp [p, R]
    field_simp [(Real.Gamma_pos_of_pos ha).ne', (Real.Gamma_pos_of_pos hb).ne']
  have hnn : 0 ≤ᵐ[volume] fun u : ℂ => ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2) :=
    ae_of_all _ fun u => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hlin := positive_riesz_lintegral_formula (a := β / 2) (b := 1 - k / 2) (z := z)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hz
  have heq : ENNReal.ofReal (∫ u : ℂ, ‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2)) =
      ENNReal.ofReal (Real.pi * (Real.Gamma (1 - β / 2) * Real.Gamma (k / 2) *
        Real.Gamma ((β - k) / 2) / (Real.Gamma (β / 2) * Real.Gamma (1 - k / 2) *
          Real.Gamma (1 + (k - β) / 2))) * ‖z‖ ^ (k - β)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (positive_riesz_convolution_integrable k β hk hβ hβ₂ z hz) hnn,
      show (fun u : ℂ => ENNReal.ofReal (‖u‖ ^ (-β) * ‖u - z‖ ^ (k - 2))) =
        fun u => ENNReal.ofReal (‖u‖ ^ (-2 * (β / 2)) * ‖u - z‖ ^ (-2 * (1 - k / 2))) by
        ext u; congr 2 <;> ring, hlin]
    congr 1
    rw [show β / 2 + (1 - k / 2) - 1 = (β - k) / 2 by ring,
      show -2 * ((β - k) / 2) = k - β by ring,
      show 1 - (1 - k / 2) = k / 2 by ring,
      show 2 - β / 2 - (1 - k / 2) = 1 + (k - β) / 2 by ring]
    ring
  have h1 : 0 < Real.Gamma (1 - β / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma (k / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h3 : 0 < Real.Gamma ((β - k) / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h4 : 0 < Real.Gamma (β / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h5 : 0 < Real.Gamma (1 - k / 2) := Real.Gamma_pos_of_pos (by linarith)
  have h6 : 0 < Real.Gamma (1 + (k - β) / 2) := Real.Gamma_pos_of_pos (by linarith)
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnn) (by positivity)).1 heq

end DOZZ.Proofs
