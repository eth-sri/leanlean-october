/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Upsilon.IntegralTaylor
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# DOZZ Upsilon integral convergence

This module contains the integrand bounds behind the convergence and strip-regularity results
for `upsilonLog`.
-/

@[expose] public section

namespace DOZZ.Proofs

noncomputable section

open Set MeasureTheory Filter Topology

def complexDenom (γ : ℝ) (t : ℂ) : ℂ :=
  Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))

def realDenom (γ : ℝ) (t : ℝ) : ℝ :=
  Real.sinh (t * γ / 4) * Real.sinh (t / γ)

/-- Numerator after putting the two terms of the integrand over a common denominator. -/
def upsilonNumerator (g w t : ℂ) : ℂ :=
  w ^ 2 * Complex.exp (-t) * (Complex.sinh (t * g / 4) * Complex.sinh (t / g)) -
    Complex.sinh (w * (t / 2)) ^ 2

def upsilonCanceledNumerator (γ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  upsilonNumerator γ ((Q γ : ℂ) / 2 - z) t

private lemma canceledNumerator_eq_source (γ : ℝ) (z : ℂ) (t : ℝ) :
    upsilonCanceledNumerator γ z t =
      (Q γ / 2 - z) ^ 2 * Real.exp (-t) *
          (Real.sinh (t * γ / 4) * Real.sinh (t / γ) : ℂ) -
        Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 := by
  simp [upsilonCanceledNumerator, upsilonNumerator, Complex.ofReal_sinh, Complex.ofReal_exp]

private lemma upsilonNumerator_deriv_eq (g w : ℂ) :
    deriv (upsilonNumerator g w) = fun t =>
      w ^ 2 * Complex.exp (-t) *
        (g / 4 * Complex.cosh (t * g / 4) * Complex.sinh (t / g) +
         g⁻¹ * Complex.sinh (t * g / 4) * Complex.cosh (t / g) -
         Complex.sinh (t * g / 4) * Complex.sinh (t / g)) -
      w * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) := by
  funext t
  unfold upsilonNumerator
  simp (disch := fun_prop) [deriv_fun_sub, deriv_fun_mul, deriv_fun_pow, deriv_div_const,
    deriv_csinh, deriv_cexp]
  ring

theorem upsilonCanceledNumerator_jet {γ : ℝ} (hγ : 0 < γ) (z : ℂ) (j : ℕ)
    (hj : j ≤ 2) : iteratedDeriv j (upsilonCanceledNumerator γ z) 0 = 0 := by
  have hc : ContDiff ℂ j (upsilonNumerator (γ : ℂ) ((Q γ : ℂ) / 2 - z)) := by
    fun_prop [upsilonNumerator]
  unfold upsilonCanceledNumerator
  rw [iteratedDeriv_comp_ofReal hc]
  interval_cases j
  · simp [upsilonNumerator]
  · simp [iteratedDeriv_one, upsilonNumerator_deriv_eq]
  · rw [iteratedDeriv_succ, iteratedDeriv_one, upsilonNumerator_deriv_eq]
    simp (disch := fun_prop) [deriv_csinh, deriv_ccosh, deriv_cexp]
    field_simp [Complex.ofReal_ne_zero.mpr hγ.ne']
    ring

section
variable {γ t : ℝ} (hγ : 0 < γ) (ht : 0 < t)
include hγ ht

lemma realDenom_ge_quadratic :
    t ^ 2 / 4 ≤ realDenom γ t := by
  have hγ'  := ne_of_gt hγ
  have hs₁ : t * γ / 4 ≤ Real.sinh (t * γ / 4) :=
    (Real.self_le_sinh_iff).2 (by positivity)
  have hs₂ : t / γ ≤ Real.sinh (t / γ) :=
    (Real.self_le_sinh_iff).2 (by positivity)
  calc
    t ^ 2 / 4 = (t * γ / 4) * (t / γ) := by field_simp [hγ']
    _ ≤ Real.sinh (t * γ / 4) * Real.sinh (t / γ) :=
      mul_le_mul hs₁ hs₂ (by positivity) (by positivity)

lemma realDenom_pos :
    0 < realDenom γ t := by
  unfold realDenom
  exact mul_pos (Real.sinh_pos_iff.2 (by positivity))
    (Real.sinh_pos_iff.2 (div_pos ht hγ))

end

section
variable {γ : ℝ} (hγ : 0 < γ) (z : ℂ)
include hγ

lemma upsilonLogIntegrand_eq_canceled_div {t : ℝ} (ht : 0 < t) :
    upsilonLogIntegrand γ z t =
      upsilonCanceledNumerator γ z t / ((realDenom γ t : ℂ) * (t : ℂ)) := by
  rw [upsilonLogIntegrand, canceledNumerator_eq_source]
  have hD  :=
    Complex.ofReal_ne_zero.mpr (realDenom_pos hγ ht).ne'
  have hS₁ : (Real.sinh (t * γ / 4) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (by positivity)).ne'
  have hS₂ : (Real.sinh (t / γ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (div_pos ht hγ)).ne'
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hRD : (realDenom γ t : ℂ) =
      (Real.sinh (t * γ / 4) : ℂ) * (Real.sinh (t / γ) : ℂ) := by
    simp [realDenom]
  rw [hRD]
  field_simp [hD, hS₁, hS₂, htC]

end

/-- Dividing a cubic bound by the denominator of the Upsilon integrand gives a bound
uniform down to zero. -/
theorem upsilon_div_norm_le {γ t C : ℝ} {N : ℂ} (hγ : 0 < γ) (ht : 0 < t)
    (hC : 0 ≤ C) (hN : ‖N‖ ≤ C * t ^ 3) :
    ‖N / ((realDenom γ t : ℂ) * (t : ℂ))‖ ≤ 4 * C := by
  have hD := realDenom_pos hγ ht
  rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hD, abs_of_pos ht, div_le_iff₀ (mul_pos hD ht)]
  calc
    ‖N‖ ≤ C * t ^ 3 := hN
    _ = (4 * C) * ((t ^ 2 / 4) * t) := by ring
    _ ≤ _ := by gcongr; exact realDenom_ge_quadratic hγ ht

theorem upsilonLogIntegrand_norm_le_of_taylor {γ t C : ℝ} (hγ : 0 < γ) (z : ℂ)
    (ht : 0 < t) (hC : 0 ≤ C) (hN : ‖upsilonCanceledNumerator γ z t‖ ≤ C * t ^ 3) :
    ‖upsilonLogIntegrand γ z t‖ ≤ 4 * C := by
  rw [upsilonLogIntegrand_eq_canceled_div hγ z ht]
  exact upsilon_div_norm_le hγ ht hC hN

lemma upsilonLogIntegrand_aestronglyMeasurable (γ : ℝ) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => upsilonLogIntegrand γ z t) volume := by
  change AEStronglyMeasurable (fun t : ℝ =>
    ((Q γ / 2 - z) ^ 2 * Real.exp (-t) -
      Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2 /
        (Real.sinh (t * γ / 4) * Real.sinh (t / γ))) / t) volume
  have hA : Measurable (fun t : ℝ => (Q γ / 2 - z) ^ 2 * Real.exp (-t)) := by
    fun_prop
  have hB : Measurable (fun t : ℝ =>
      Complex.sinh ((Q γ / 2 - z) * (t / 2)) ^ 2) := by
    fun_prop
  have hD : Measurable (fun t : ℝ =>
      (Real.sinh (t * γ / 4) : ℂ) * (Real.sinh (t / γ) : ℂ)) := by
    fun_prop
  have ht : Measurable (fun t : ℝ => (t : ℂ)) := by
    fun_prop
  exact ((hA.sub (hB.div hD)).div ht).aestronglyMeasurable
private lemma upsilonLogIntegrand_integrableOn_Ioc {γ : ℝ} (hγ : 0 < γ) (z : ℂ) :
    IntegrableOn (upsilonLogIntegrand γ z) (Ioc 0 1) := by
  have hc : ContDiff ℂ 3 (upsilonNumerator (γ : ℂ) ((Q γ : ℂ) / 2 - z)) := by
    fun_prop [upsilonNumerator]
  have hr : ContDiff ℝ 3 (upsilonCanceledNumerator γ z) :=
    (hc.restrict_scalars ℝ).comp Complex.ofRealCLM.contDiff
  obtain ⟨C, hC, hb⟩ := exists_uniform_cubic_bound (K := {(0 : ℝ)})
    (F := fun p => upsilonCanceledNumerator γ z p.2) isCompact_singleton
    (fun _ _ => (hr.comp contDiff_snd).contDiffAt) (fun _ _ => upsilonCanceledNumerator_jet hγ z)
  refine Measure.integrableOn_of_bounded (M := 4 * C) (by simp)
    (upsilonLogIntegrand_aestronglyMeasurable γ z) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact upsilonLogIntegrand_norm_le_of_taylor hγ z ht.1 hC (hb 0 rfl t ⟨ht.1.le, ht.2⟩)

def tailConst (γ : ℝ) : ℝ :=
  ((1 - Real.exp (-2 * (γ / 4))) / 2) *
    ((1 - Real.exp (-2 * (1 / γ))) / 2)

lemma tailConst_pos {γ : ℝ} (hγ : 0 < γ) : 0 < tailConst γ := by
  have hγ4 : 0 < γ / 4 := by positivity
  have hγinv : 0 < 1 / γ := by positivity
  have h₁ : -2 * (γ / 4) < 0 := by linarith only [hγ4]
  have h₂ : -2 * (1 / γ) < 0 := by linarith only [hγinv]
  have h₁'  :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr h₁)
  have h₂'  :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr h₂)
  unfold tailConst
  exact mul_pos (div_pos h₁' (by norm_num)) (div_pos h₂' (by norm_num))

private lemma real_sinh_ge_exp {a x : ℝ} (hax : a ≤ x) :
    ((1 - Real.exp (-2 * a)) / 2) * Real.exp x ≤ Real.sinh x := by
  have he : Real.exp x * Real.exp (-2 * x) = Real.exp (-x) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Real.sinh_eq, ← he]
  have h := Real.exp_le_exp.mpr (show -2 * x ≤ -2 * a by linarith)
  nlinarith [mul_le_mul_of_nonneg_left h (Real.exp_nonneg x)]

lemma realDenom_ge_tail_exp {γ t : ℝ} (hγ : 0 < γ) (ht : 1 ≤ t) :
    tailConst γ * Real.exp (Q γ / 2 * t) ≤ realDenom γ t := by
  have hs₁ : ((1 - Real.exp (-2 * (γ / 4))) / 2) * Real.exp (t * γ / 4) ≤
      Real.sinh (t * γ / 4) :=
    real_sinh_ge_exp (by linarith only [mul_le_mul_of_nonneg_right ht hγ.le])
  have hs₂ := real_sinh_ge_exp (div_le_div_of_nonneg_right ht (by positivity))
  have hq : Q γ / 2 * t = t * γ / 4 + t / γ := by
    unfold Q
    ring
  have hc₂ : 0 < (1 - Real.exp (-2 * (1 / γ))) / 2 := by
    apply div_pos
    simpa
    · norm_num
  have hsecond : 0 ≤ ((1 - Real.exp (-2 * (1 / γ))) / 2) * Real.exp (t / γ) :=
    le_of_lt (mul_pos hc₂ (Real.exp_pos _))
  have hfirst : 0 ≤ Real.sinh (t * γ / 4) :=
    (Real.sinh_pos_iff.mpr (by positivity)).le
  calc
    tailConst γ * Real.exp (Q γ / 2 * t) =
        (((1 - Real.exp (-2 * (γ / 4))) / 2) * Real.exp (t * γ / 4)) *
          (((1 - Real.exp (-2 * (1 / γ))) / 2) * Real.exp (t / γ)) := by
            unfold tailConst
            have he : Real.exp (Q γ / 2 * t) =
                Real.exp (t * γ / 4) * Real.exp (t / γ) := by
              rw [← Real.exp_add, hq]
            rw [he]
            ring
    _ ≤ Real.sinh (t * γ / 4) * Real.sinh (t / γ) :=
      mul_le_mul hs₁ hs₂ hsecond hfirst
    _ = realDenom γ t := by rfl

private lemma exp_abs_re_bound {w u : ℂ}
    (h : ‖u‖ ≤ ‖Complex.exp w‖ + ‖Complex.exp (-w)‖) :
    ‖u / 2‖ ≤ Real.exp |w.re| := by
  rw [norm_div]
  have h₁ := Real.exp_le_exp.mpr (le_abs_self w.re)
  have h₂ := Real.exp_le_exp.mpr (neg_le_abs w.re)
  simp only [Complex.norm_exp, Complex.neg_re] at h
  norm_num
  linarith

lemma complex_sinh_norm_le_exp_abs_re (w : ℂ) : ‖Complex.sinh w‖ ≤ Real.exp |w.re| :=
  exp_abs_re_bound (norm_sub_le _ _)

lemma complex_cosh_norm_le_exp_abs_re (w : ℂ) : ‖Complex.cosh w‖ ≤ Real.exp |w.re| :=
  exp_abs_re_bound (norm_add_le _ _)

lemma complex_half_argument_mul_norm_le {t : ℝ} (ht : 0 ≤ t) (w : ℂ) {a b : ℂ}
    (ha : ‖a‖ ≤ Real.exp |(w * (t / 2)).re|) (hb : ‖b‖ ≤ Real.exp |(w * (t / 2)).re|) :
    ‖a * b‖ ≤ Real.exp (|w.re| * t) := by
  rw [norm_mul]
  refine (mul_le_mul ha hb (norm_nonneg _) (Real.exp_nonneg _)).trans_eq ?_
  have he : (w * (t / 2)).re = w.re * (t / 2) := by simp
  rw [← Real.exp_add, he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
  congr 1
  ring

lemma upsilon_tail_ratio {γ t x : ℝ} {N : ℂ} (hγ : 0 < γ) (ht : 1 ≤ t)
    (hN : ‖N‖ ≤ Real.exp (x * t)) :
    ‖N / (realDenom γ t : ℂ)‖ ≤ (tailConst γ)⁻¹ * Real.exp (-(Q γ / 2 - x) * t) := by
  have hD := realDenom_pos hγ (by linarith : 0 < t)
  have hk := tailConst_pos hγ
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hD, div_le_iff₀ hD]
  refine hN.trans ?_
  calc
    _ = (tailConst γ)⁻¹ * Real.exp (-(Q γ / 2 - x) * t) *
          (tailConst γ * Real.exp (Q γ / 2 * t)) := by
      rw [← show - (Q γ / 2 - x) * t + Q γ / 2 * t = x * t by ring, Real.exp_add]
      field_simp [(tailConst_pos hγ).ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (realDenom_ge_tail_exp hγ ht) (by positivity :
      0 ≤ (tailConst γ)⁻¹ * Real.exp (-(Q γ / 2 - x) * t))

lemma upsilonLogIntegrand_norm_le_tail {γ : ℝ} (hγ : 0 < γ)
    (z : ℂ) (_hz0 : 0 < z.re) (_hzQ : z.re < Q γ) {t : ℝ} (ht : 1 ≤ t) :
    ‖upsilonLogIntegrand γ z t‖ ≤ ‖(Q γ / 2 : ℂ) - z‖ ^ 2 * Real.exp (-t) +
        (tailConst γ)⁻¹ * Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) := by
  let w := (Q γ / 2 : ℂ) - z
  have hS := complex_sinh_norm_le_exp_abs_re (w * (t / 2))
  have hb' : ‖Complex.sinh (w * (t / 2)) ^ 2‖ ≤ Real.exp (|w.re| * t) := by
    rw [pow_two]
    exact complex_half_argument_mul_norm_le (zero_le_one.trans ht) w hS hS
  have hb := upsilon_tail_ratio hγ ht hb' 
  have ht' : ‖(t : ℂ)‖ = t := by simp [abs_of_pos (by linarith : 0 < t)]
  have hD : (realDenom γ t : ℂ) = (Real.sinh (t * γ / 4) : ℂ) * (Real.sinh (t / γ) : ℂ) := by
    simp [realDenom]
  unfold upsilonLogIntegrand
  rw [← hD]
  change ‖(w ^ 2 * Real.exp (-t) - Complex.sinh (w * (t / 2)) ^ 2 / (realDenom γ t : ℂ)) / (t : ℂ)‖ ≤ _
  rw [norm_div, ht']
  refine (div_le_self (norm_nonneg _) ht).trans ((norm_sub_le _ _).trans ?_)
  rw [norm_mul, norm_pow, show ‖(Real.exp (-t) : ℂ)‖ = Real.exp (-t) by
    simp [Complex.norm_exp]]
  exact add_le_add le_rfl (by simpa only [show w.re = Q γ / 2 - z.re by simp [w]] using hb)

section
variable {γ : ℝ} (hγ : 0 < γ)
include hγ

private lemma upsilonLogIntegrand_integrableOn_Ioi_one
    (z : ℂ) (hz0 : 0 < z.re) (hzQ : z.re < Q γ) :
    IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ z t) (Ioi 1) := by
  let w  := (Q γ / 2 : ℂ) - z
  let δ  := Q γ / 2 - |w.re|
  let A  := ‖(Q γ / 2 : ℂ) - z‖ ^ 2
  let B  := (tailConst γ)⁻¹
  have hstrip : |w.re| < Q γ / 2 := by
    apply (abs_lt).2
    constructor <;> dsimp [w] <;> simp <;> linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hmajor1 : IntegrableOn (fun t : ℝ => A * Real.exp (-t)) (Ioi 1) := by
    change Integrable (fun t : ℝ => A * Real.exp (-t)) (volume.restrict (Ioi 1))
    simpa [mul_comm] using (exp_neg_integrableOn_Ioi 1 (b := 1) (by norm_num)).const_mul A
  have hmajor2 : IntegrableOn (fun t : ℝ => B * Real.exp (-δ * t)) (Ioi 1) := by
    change Integrable (fun t : ℝ => B * Real.exp (-δ * t)) (volume.restrict (Ioi 1))
    simpa [mul_comm] using (exp_neg_integrableOn_Ioi 1 (b := δ) hδ).const_mul B
  have hmajor := hmajor1.add hmajor2
  apply Integrable.mono' hmajor
    (upsilonLogIntegrand_aestronglyMeasurable γ z).restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have htail := upsilonLogIntegrand_norm_le_tail hγ z hz0 hzQ ht.le
  simpa [w, δ, A, B, tailConst, mul_comm] using htail

theorem upsilonLogIntegrand_integrableOn
    (_hγ2 : γ < 2) (z : ℂ) (hz0 : 0 < z.re) (hzQ : z.re < Q γ) :
    IntegrableOn (fun t : ℝ => upsilonLogIntegrand γ z t) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    norm_num
  rw [hsplit, integrableOn_union]
  exact ⟨upsilonLogIntegrand_integrableOn_Ioc hγ z,
    upsilonLogIntegrand_integrableOn_Ioi_one hγ z hz0 hzQ⟩

end


end

end DOZZ.Proofs

end
