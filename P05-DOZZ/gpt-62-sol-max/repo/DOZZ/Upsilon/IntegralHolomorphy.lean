/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import DOZZ.Statements.Defs.DualMu
public import DOZZ.Upsilon.IntegralBounds
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# DOZZ Upsilon integral holomorphy

Differentiation under the defining integral on its strip of convergence.
-/

@[expose] public section

namespace DOZZ.Proofs

noncomputable section

open Set MeasureTheory Filter Topology

private def zDerivNumComplex (γ : ℝ) (w t : ℂ) : ℂ :=
  -2 * w * Complex.exp (-t) * complexDenom γ t +
    t * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))

private def zDerivNum (γ : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  zDerivNumComplex γ w (t : ℂ)

private def zDerivNumJoint (γ : ℝ) (p : ℂ × ℝ) : ℂ :=
  zDerivNum γ p.1 p.2

section
variable (γ : ℝ)

private lemma zDerivNumJoint_contDiff :
    ContDiff ℝ 3 (zDerivNumJoint γ) := by
  have hF : ContDiff ℂ 3 (fun q : ℂ × ℂ => zDerivNumComplex γ q.1 q.2) := by
    fun_prop [zDerivNumComplex, complexDenom]
  have hF'  :=
    hF.restrict_scalars ℝ
  have hPair : ContDiff ℝ 3 (fun p : ℂ × ℝ => (p.1, (p.2 : ℂ))) := contDiff_fst.prodMk (Complex.ofRealCLM.contDiff.comp contDiff_snd)
  change ContDiff ℝ 3 ((fun q : ℂ × ℂ => zDerivNumComplex γ q.1 q.2) ∘
    fun p : ℂ × ℝ => (p.1, (p.2 : ℂ)))
  exact hF'.comp hPair

private lemma zDerivNumComplex_deriv_eq (w : ℂ) :
    deriv (zDerivNumComplex γ w) = fun t =>
      -2 * w * Complex.exp (-t) *
          ((γ : ℂ) / 4 * Complex.cosh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ)) +
            (γ : ℂ)⁻¹ * Complex.sinh (t * (γ : ℂ) / 4) * Complex.cosh (t / (γ : ℂ))) +
        2 * w * Complex.exp (-t) * complexDenom γ t +
    Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) +
        t * w / 2 * (Complex.cosh (w * (t / 2)) ^ 2 + Complex.sinh (w * (t / 2)) ^ 2) := by
  funext t
  change deriv (fun t : ℂ =>
      -2 * w * Complex.exp (-t) *
          (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) +
        t * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))) t = _
  simp (disch := fun_prop) [complexDenom, deriv_csinh, deriv_ccosh, deriv_cexp]
  ring_nf

private lemma zDerivNumComplex_deriv_zero (w : ℂ) :
    deriv (zDerivNumComplex γ w) 0 = 0 := by
  rw [zDerivNumComplex_deriv_eq]
  simp [complexDenom]

end

private lemma zDerivNumComplex_iteratedDeriv_two_zero {γ : ℝ} (hγ : 0 < γ) (w : ℂ) :
    iteratedDeriv 2 (zDerivNumComplex γ w) 0 = 0 := by
  rw [iteratedDeriv_succ]
  rw [show iteratedDeriv 1 (zDerivNumComplex γ w) = deriv (zDerivNumComplex γ w) by simp]
  rw [zDerivNumComplex_deriv_eq]
  simp (disch := fun_prop) [complexDenom, deriv_csinh, deriv_ccosh, deriv_cexp]
  have hγC : (γ : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hγ)
  field_simp [hγC]
  ring

private lemma zDerivNum_jet {γ : ℝ} (hγ : 0 < γ) (w : ℂ) (j : ℕ) (hj : j ≤ 2) :
    iteratedDeriv j (zDerivNum γ w) 0 = 0 := by
  change iteratedDeriv j (fun t : ℝ => zDerivNumComplex γ w t) 0 = 0
  rw [iteratedDeriv_comp_ofReal (by fun_prop [zDerivNumComplex, complexDenom])]
  interval_cases j
  · simp [zDerivNumComplex, complexDenom]
  · simpa [iteratedDeriv_one] using zDerivNumComplex_deriv_zero γ w
  · exact zDerivNumComplex_iteratedDeriv_two_zero hγ w

private lemma exists_zDerivNum_taylor_bound {γ : ℝ} (hγ : 0 < γ) (w₀ : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.closedBall w₀ r, ∀ t ∈ Icc 0 1,
      ‖zDerivNum γ w t‖ ≤ C * t ^ 3 :=
  exists_uniform_cubic_bound (F := zDerivNumJoint γ) (isCompact_closedBall _ _)
    (fun _ _ => (zDerivNumJoint_contDiff γ).contDiffAt) (fun w _ => zDerivNum_jet hγ w)

private def upsilonLogIntegrandDeriv (γ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  zDerivNum γ ((Q γ / 2 : ℂ) - z) t /
    ((realDenom γ t : ℂ) * (t : ℂ))

private lemma deriv_upsilonLogIntegrand {γ : ℝ} {t : ℝ}
    (hγ : 0 < γ) (ht : 0 < t) (z : ℂ) :
    deriv (fun z : ℂ => upsilonLogIntegrand γ z t) z =
      upsilonLogIntegrandDeriv γ z t := by
  simp_rw [upsilonLogIntegrand_eq_canceled_div hγ _ ht]
  simp (disch := fun_prop) [upsilonCanceledNumerator, upsilonNumerator, upsilonLogIntegrandDeriv,
    zDerivNum, zDerivNumComplex, complexDenom, deriv_div_const, deriv_csinh, deriv_sub_const]
  ring

section
variable {γ : ℝ} (hγ : 0 < γ) (z : ℂ)
include hγ

private lemma upsilonLogIntegrandDeriv_norm_le_of_taylor (C : ℝ) (hC : 0 ≤ C)
    {t : ℝ} (ht : 0 < t) (_ht1 : t ≤ 1)
    (hTaylor : ‖zDerivNum γ ((Q γ / 2 : ℂ) - z) t‖ ≤ C * t ^ 3) :
    ‖upsilonLogIntegrandDeriv γ z t‖ ≤ 4 * C :=
  upsilon_div_norm_le hγ ht hC hTaylor

private lemma upsilonLogIntegrandDeriv_norm_le_tail (_hz0 : 0 < z.re) (_hzQ : z.re < Q γ) {t : ℝ} (ht : 1 ≤ t) :
    ‖upsilonLogIntegrandDeriv γ z t‖ ≤
      2 * ‖(Q γ / 2 : ℂ) - z‖ * Real.exp (-t) +
        (tailConst γ)⁻¹ * Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) := by
  let w := (Q γ / 2 : ℂ) - z
  let v := w * ((t : ℂ) / 2)
  have ht0 : 0 < t := by linarith
  have htC := Complex.ofReal_ne_zero.mpr ht0.ne'
  have hD := Complex.ofReal_ne_zero.mpr (realDenom_pos hγ ht0).ne'
  have he : upsilonLogIntegrandDeriv γ z t =
      (-2 * w * Complex.exp (-t)) / (t : ℂ) + (Complex.sinh v * Complex.cosh v) / (realDenom γ t : ℂ) := by
    change (-2 * w * Complex.exp (-(t : ℂ)) * complexDenom γ t + (t : ℂ) * Complex.sinh v * Complex.cosh v) /
      ((realDenom γ t : ℂ) * (t : ℂ)) = _
    rw [show complexDenom γ (t : ℂ) = (realDenom γ t : ℂ) by simp [complexDenom, realDenom]]
    field_simp
  have hB := upsilon_tail_ratio hγ ht (complex_half_argument_mul_norm_le ht0.le w
    (complex_sinh_norm_le_exp_abs_re v) (complex_cosh_norm_le_exp_abs_re v))
  have hA := div_le_self (norm_nonneg (-2 * w * Complex.exp (-(t : ℂ)))) ht
  rw [he]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · simpa [norm_div, abs_of_pos ht0, Complex.norm_exp] using hA
  · simpa [w, Complex.sub_re] using hB

end

private lemma upsilonLogIntegrandDeriv_aestronglyMeasurable (γ : ℝ) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => upsilonLogIntegrandDeriv γ z t) volume := by
  have hnum : Measurable (fun t : ℝ => zDerivNum γ ((Q γ / 2 : ℂ) - z) t) := by
    fun_prop [zDerivNum, zDerivNumComplex, complexDenom]
  have hden : Measurable (fun t : ℝ =>
      (realDenom γ t : ℂ) * (t : ℂ)) := by
    fun_prop [realDenom]
  exact (hnum.div hden).aestronglyMeasurable

section
variable {γ : ℝ} (hγ : 0 < γ)
include hγ

private lemma upsilonLog_hasDerivAt (hγ2 : γ < 2)
    (z₀ : ℂ) (hz₀ : 0 < z₀.re) (hzQ : z₀.re < Q γ) :
    HasDerivAt (fun z : ℂ => upsilonLog γ z)
      (∫ t in Ioi (0 : ℝ), upsilonLogIntegrandDeriv γ z₀ t) z₀ := by
  let margin : ℝ := min z₀.re (Q γ - z₀.re)
  let r : ℝ := margin / 2
  let q : ℂ := (Q γ / 2 : ℂ)
  let w₀ : ℂ := q - z₀
  let W : ℝ := ‖w₀‖ + r
  let B : ℝ := (tailConst γ)⁻¹
  have hmargin : 0 < margin := by
    positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hQpos := Q_pos hγ
  have hqre : q.re = Q γ / 2 := by simp [q]
  have hWnonneg : 0 ≤ W := by dsimp [W]; positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact le_of_lt (inv_pos.mpr (tailConst_pos hγ))
  obtain ⟨C, hC, hTaylor⟩ := exists_zDerivNum_taylor_bound hγ w₀ r
  let A : ℝ := 4 * C * Real.exp 1 + 2 * W
  let bound : ℝ → ℝ := fun t => A * Real.exp (-t) + B * Real.exp (-r * t)
  have hA_nonneg : 0 ≤ A := by positivity
  have hA_lower : 2 * W ≤ A := by
    dsimp [A]
    linarith only [mul_nonneg hC (Real.exp_pos 1).le]
  have hs : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr
  have hz_near (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
      |z.re - z₀.re| < r := by
    have hdist : dist z z₀ < r := Metric.mem_ball.mp hz
    have hre := (Complex.abs_re_le_norm (z - z₀)).trans_lt (by
      simpa [dist_eq_norm] using hdist)
    simpa [Complex.sub_re] using hre
  have hz_real_bounds (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
      r < z.re ∧ z.re < Q γ - r := by
    have hc := hz_near z hz
    have hc' := abs_lt.mp hc
    have hmleft : margin ≤ z₀.re := min_le_left _ _
    have hmright : margin ≤ Q γ - z₀.re := min_le_right _ _
    constructor
    · dsimp [r] at hc' ⊢
      dsimp [margin] at hmleft
      linarith
    · dsimp [r] at hc' ⊢
      dsimp [margin] at hmright
      linarith
  have hw_re_margin (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
      |Q γ / 2 - z.re| ≤ Q γ / 2 - r := by
    obtain ⟨hzlow, hzhigh⟩ := hz_real_bounds z hz
    apply abs_le.mpr
    constructor <;> linarith
  have hw_norm_bound (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
      ‖(Q γ / 2 : ℂ) - z‖ ≤ W := by
    have hdist : dist z z₀ < r := Metric.mem_ball.mp hz
    have hdiff : dist ((Q γ / 2 : ℂ) - z) w₀ = dist z z₀ := by
      rw [dist_eq_norm, dist_eq_norm]
      have heq : ((Q γ / 2 : ℂ) - z) - w₀ = z₀ - z := by dsimp [w₀]; ring
      rw [heq]
      simp [norm_sub_rev]
    dsimp [W, w₀]
    calc
      ‖(Q γ / 2 : ℂ) - z‖ = ‖w₀ + (z₀ - z)‖ := by
        congr 1
        dsimp [w₀]
        ring
      _ ≤ ‖w₀‖ + ‖z₀ - z‖ := norm_add_le _ _
      _ = ‖w₀‖ + dist z z₀ := by rw [dist_eq_norm]; simp [norm_sub_rev]
      _ ≤ ‖w₀‖ + r := by linarith [hdiff]
  have hTaylor_local {z : ℂ} (hz : z ∈ Metric.ball z₀ r)
      {t : ℝ} (ht : t ∈ Icc 0 1) :
      ‖zDerivNum γ ((Q γ / 2 : ℂ) - z) t‖ ≤ C * t ^ 3 := by
    apply hTaylor
    · have hdist : dist ((Q γ / 2 : ℂ) - z) w₀ ≤ r := by
        rw [dist_eq_norm]
        have heq : ((Q γ / 2 : ℂ) - z) - w₀ = z₀ - z := by dsimp [w₀]; ring
        rw [heq]
        have hdz  := Metric.mem_ball.mp hz
        simpa [dist_eq_norm, norm_sub_rev] using hdz.le
      assumption
    · exact ht
  have hparam_bound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball z₀ r,
        ‖upsilonLogIntegrandDeriv γ z t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    by_cases ht1 : t ≤ 1
    · have hTaylor' := hTaylor_local hz ⟨le_of_lt ht, ht1⟩
      have hsmall := upsilonLogIntegrandDeriv_norm_le_of_taylor hγ z C hC ht ht1 hTaylor'
      have hexp : 1 ≤ Real.exp (1 - t) := by
        simpa
      have hexpId : Real.exp (1 - t) = Real.exp 1 * Real.exp (-t) := by
        rw [← Real.exp_add]
        congr 1
      have hcoeff : 4 * C ≤ A * Real.exp (-t) := by
        dsimp [A]
        have h := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 4 * C)
        rw [hexpId] at h
        linarith only [h, mul_nonneg hWnonneg (Real.exp_pos (-t)).le]
      calc
        _ ≤ 4 * C := hsmall
        _ ≤ A * Real.exp (-t) := hcoeff
        _ ≤ bound t := by
          dsimp [bound]
          exact le_add_of_nonneg_right (mul_nonneg hB_nonneg (Real.exp_pos _).le)
    · have ht'  := le_of_not_ge ht1
      obtain ⟨hzlow, hzhigh⟩ := hz_real_bounds z hz
      have hzQ' : z.re < Q γ := lt_of_lt_of_le hzhigh (by linarith [hr])
      have htail := upsilonLogIntegrandDeriv_norm_le_tail hγ z (lt_trans hr hzlow) hzQ' ht'
      have hδ : r ≤ Q γ / 2 - |Q γ / 2 - z.re| := by
        have habs := hw_re_margin z hz
        linarith
      have hfirst :
          2 * ‖(Q γ / 2 : ℂ) - z‖ * Real.exp (-t) ≤ A * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right (by
          calc
            2 * ‖(Q γ / 2 : ℂ) - z‖ ≤ 2 * W := mul_le_mul_of_nonneg_left (hw_norm_bound z hz) (by norm_num)
            _ ≤ A := hA_lower) (Real.exp_pos _).le
      have hsecond :
          B * Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) ≤
            B * Real.exp (-r * t) := by
        apply mul_le_mul_of_nonneg_left _ hB_nonneg
        apply Real.exp_le_exp.mpr
        have ht0 : 0 ≤ t := by linarith
        have hmul := mul_le_mul_of_nonneg_right hδ ht0
        linarith only [hmul]
      have htail' := add_le_add hfirst hsecond
      simpa [bound, B] using htail.trans htail'
  have hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun t : ℝ => upsilonLogIntegrand γ z t)
        (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [] with z
    exact (upsilonLogIntegrand_aestronglyMeasurable γ z).restrict
  have hF_int := (upsilonLogIntegrand_integrableOn hγ hγ2 z₀ hz₀ hzQ)
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => upsilonLogIntegrandDeriv γ z₀ t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (upsilonLogIntegrandDeriv_aestronglyMeasurable γ z₀).restrict
  have hBound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    have h₁ : IntegrableOn (fun t : ℝ => A * Real.exp (-t)) (Ioi (0 : ℝ)) := by
      change Integrable (fun t : ℝ => A * Real.exp (-t))
        (volume.restrict (Ioi (0 : ℝ)))
      simpa [mul_comm] using
        (exp_neg_integrableOn_Ioi 0 (b := 1) (by norm_num)).const_mul A
    have h₂ : IntegrableOn (fun t : ℝ => B * Real.exp (-r * t)) (Ioi (0 : ℝ)) := by
      change Integrable (fun t : ℝ => B * Real.exp (-r * t))
        (volume.restrict (Ioi (0 : ℝ)))
      simpa [mul_comm] using
        (exp_neg_integrableOn_Ioi 0 (b := r) hr).const_mul B
    change IntegrableOn (fun t : ℝ => A * Real.exp (-t) + B * Real.exp (-r * t))
      (Ioi (0 : ℝ))
    exact h₁.add h₂
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball z₀ r,
        HasDerivAt (fun z : ℂ => upsilonLogIntegrand γ z t)
          (upsilonLogIntegrandDeriv γ z t) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hfun : DifferentiableAt ℂ (fun z : ℂ => upsilonLogIntegrand γ z t) z := by
      fun_prop [upsilonLogIntegrand]
    simpa [deriv_upsilonLogIntegrand hγ ht z] using hfun.hasDerivAt
  obtain ⟨_, hhas⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball z₀ r) hs hF_meas hF_int hF'_meas hparam_bound hBound_int hdiff
  simpa

/-- The logarithm given by the convergent integral is holomorphic on its defining strip. -/
theorem upsilonLog_differentiableOn (_hγ2 : γ < 2) :
    DifferentiableOn ℂ (fun z => upsilonLog γ z)
      {z | 0 < z.re ∧ z.re < Q γ} := by
  intro z hz
  exact (upsilonLog_hasDerivAt hγ _hγ2 z hz.1 hz.2).differentiableAt.differentiableWithinAt

end

end

end DOZZ.Proofs

end
