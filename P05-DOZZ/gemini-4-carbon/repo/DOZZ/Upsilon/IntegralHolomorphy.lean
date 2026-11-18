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
-/

@[expose] public section

namespace DOZZ.Proofs

noncomputable section

variable {γ : ℝ}

open Set MeasureTheory Filter Topology

private def zDerivNumComplex (γ : ℝ) (w t : ℂ) : ℂ :=
  -2 * w * Complex.exp (-t) * complexDenom γ t +
    t * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))

private def zDerivNum (γ : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  zDerivNumComplex γ w (t : ℂ)




private def upsilonLogIntegrandDeriv (γ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  zDerivNum γ ((Q γ / 2 : ℂ) - z) t / ((realDenom γ t : ℂ) * (t : ℂ))



/-- The logarithm given by the convergent integral is holomorphic on its defining strip. -/
theorem upsilonLog_differentiableOn
    (hγ : 0 < γ) (hγ2 : γ < 2) :
    DifferentiableOn ℂ (fun z => upsilonLog γ z) {z | 0 < z.re ∧ z.re < Q γ} := by
  have exists_zDerivNum_taylor_bound (w₀ : ℂ) (r : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.closedBall w₀ r, ∀ t ∈ Icc 0 1,
        ‖zDerivNum γ w t‖ ≤ C * t ^ 3 := by
    have zDerivNum_third_continuous (γ : ℝ) : Continuous fun p : ℂ × ℝ => iteratedDeriv 3 (zDerivNum γ p.1) p.2 := by
      let J (p : ℂ × ℝ) : ℂ := zDerivNum γ p.1 p.2
      have hJ : ContDiff ℝ 3 J :=
        ((by fun_prop [zDerivNumComplex, complexDenom] :
          ContDiff ℂ 3 fun q : ℂ × ℂ => zDerivNumComplex γ q.1 q.2).restrict_scalars ℝ).comp
          (contDiff_fst.prodMk (Complex.ofRealCLM.contDiff.comp contDiff_snd))
      have hEq : (fun p : ℂ × ℝ => iteratedDeriv 3 (zDerivNum γ p.1) p.2) =
          fun p : ℂ × ℝ => iteratedFDeriv ℝ 3 J p (fun _ : Fin 3 => (0, (1 : ℝ))) := by
        funext p
        let line (t : ℝ) : ℂ × ℝ := (p.1, t)
        have hd : deriv line = fun _ => (0, (1 : ℝ)) :=
          funext fun t => ((hasDerivAt_const t p.1).prodMk (hasDerivAt_id t)).deriv
        have hd2 : iteratedDeriv 2 line = fun _ => 0 := by
          funext t; rw [iteratedDeriv_succ, show iteratedDeriv 1 line = deriv line by simp, hd]; simp
        have hd3 : iteratedDeriv 3 line p.2 = 0 := by rw [iteratedDeriv_succ, hd2]; simp
        have hc := iteratedDeriv_vcomp_three (hg := hJ.contDiffAt) (hf := (by fun_prop : ContDiffAt ℝ 3 line p.2))
        rw [congrFun hd2 p.2, hd3] at hc
        simp only [line, hd, ContinuousLinearMap.map_zero, add_zero] at hc
        rw [ContinuousMultilinearMap.map_coord_zero (iteratedFDeriv ℝ 2 J (p.1, p.2)) 0 (by simp),
          ContinuousMultilinearMap.map_coord_zero (iteratedFDeriv ℝ 2 J (p.1, p.2)) 1 (by simp)] at hc
        simpa [Function.comp_def, J] using hc
      rw [hEq]; fun_prop
    have zDerivNumContDiff (γ : ℝ) (w : ℂ) : ContDiff ℝ 3 (zDerivNum γ w) := 
      ((by fun_prop [zDerivNumComplex, complexDenom] : ContDiff ℂ 3 (zDerivNumComplex γ w)).restrict_scalars ℝ).comp
        Complex.ofRealCLM.contDiff
    have hd_eq (w : ℂ) : deriv (zDerivNumComplex γ w) = fun t =>
        -2 * w * Complex.exp (-t) *
            ((γ : ℂ) / 4 * Complex.cosh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ)) +
              (γ : ℂ)⁻¹ * Complex.sinh (t * (γ : ℂ) / 4) * Complex.cosh (t / (γ : ℂ))) +
          2 * w * Complex.exp (-t) * complexDenom γ t +
          Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) +
          t * w / 2 * (Complex.cosh (w * (t / 2)) ^ 2 + Complex.sinh (w * (t / 2)) ^ 2) := by
      funext t
      change deriv (fun t : ℂ => -2 * w * Complex.exp (-t) *
          (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) +
        t * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))) t = _
      simp (disch := fun_prop) [complexDenom, deriv_csinh, deriv_ccosh, deriv_cexp]; ring_nf
    have htay0 (w : ℂ) (t : ℝ) : taylorWithinEval (zDerivNum γ w) 2 (Icc 0 1) 0 t = 0 := by
      have hF : Differentiable ℂ (zDerivNumComplex γ w) :=
        (by fun_prop [zDerivNumComplex, complexDenom] : ContDiff ℂ 1 (zDerivNumComplex γ w)).differentiable one_ne_zero
      have hd1_fun : deriv (zDerivNum γ w) = fun s : ℝ => deriv (zDerivNumComplex γ w) (s : ℂ) :=
        funext fun s => (hF s).hasDerivAt.comp_ofReal.deriv
      have hd1 : deriv (zDerivNum γ w) 0 = 0 := by rw [hd1_fun, hd_eq]; simp [complexDenom]
      have hd2 : iteratedDeriv 2 (zDerivNum γ w) 0 = 0 := by
        have hF' : Differentiable ℂ (deriv (zDerivNumComplex γ w)) := by rw [hd_eq]; fun_prop [complexDenom]
        rw [iteratedDeriv_succ, show iteratedDeriv 1 (zDerivNum γ w) = deriv (zDerivNum γ w) by simp,
          hd1_fun, (hF' (0 : ℂ)).hasDerivAt.comp_ofReal.deriv, hd_eq]
        simp (disch := fun_prop) [complexDenom, deriv_csinh, deriv_ccosh, deriv_cexp]
        field_simp [mod_cast hγ.ne']; ring
      have hu := uniqueDiffOn_Icc (zero_lt_one' ℝ)
      have hw1 := iteratedDerivWithin_eq_iteratedDeriv hu
        (show ContDiffAt ℝ 1 (zDerivNum γ w) 0 from (zDerivNumContDiff γ w).contDiffAt.of_le (by norm_num)) (by simp)
      have hw2 := iteratedDerivWithin_eq_iteratedDeriv hu
        (show ContDiffAt ℝ 2 (zDerivNum γ w) 0 from (zDerivNumContDiff γ w).contDiffAt.of_le (by norm_num)) (by simp)
      rw [taylor_within_apply]
      simp [Finset.sum_range_succ, zDerivNum, zDerivNumComplex, complexDenom, hw1, hw2, hd1, hd2]
    let K : Set (ℂ × ℝ) := Metric.closedBall w₀ r ×ˢ Icc 0 1
    obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall w₀ r |>.prod isCompact_Icc).bddAbove_image
      (zDerivNum_third_continuous γ).norm.continuousOn
    let C := max C₀ 0
    refine ⟨C, le_max_right _ _, fun w hw t ht => ?_⟩
    have hTaylor := taylor_mean_remainder_bound (f := zDerivNum γ w) (a := 0) (b := 1) (C := C) (x := t) (n := 2)
      zero_le_one (zDerivNumContDiff γ w).contDiffOn ht fun y hy => by
        rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc zero_lt_one) (zDerivNumContDiff γ w).contDiffAt hy]
        exact (hC₀ ⟨(w, y), ⟨hw, hy⟩, rfl⟩).trans (le_max_left C₀ 0)
    rw [htay0 w t] at hTaylor; norm_num at hTaylor
    linarith [hTaylor, mul_nonneg (le_max_right C₀ 0) (pow_nonneg ht.1 3)]
  have upsilonLogIntegrandDeriv_norm_le_tail (z : ℂ) (_hz0 : 0 < z.re) (_hzQ : z.re < Q γ) {t : ℝ} (ht : 1 ≤ t) : ‖upsilonLogIntegrandDeriv γ z t‖ ≤
        2 * ‖(Q γ / 2 : ℂ) - z‖ * Real.exp (-t) +
          (tailConst γ)⁻¹ * Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) := by
    let w := (Q γ / 2 : ℂ) - z
    let δ := Q γ / 2 - |w.re|
    have ht0 : 0 < t := by linarith
    have hdenPos := realDenom_pos hγ ht0
    have hK := tailConst_pos hγ
    have hEq : upsilonLogIntegrandDeriv γ z t =
        (-2 * w * Complex.exp (-(t : ℂ)) * complexDenom γ (t : ℂ) / ((realDenom γ t : ℂ) * (t : ℂ))) +
          (Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) / (realDenom γ t : ℂ)) := by
      rw [upsilonLogIntegrandDeriv, zDerivNum, zDerivNumComplex]
      field_simp [Complex.ofReal_ne_zero.mpr ht0.ne', Complex.ofReal_ne_zero.mpr hdenPos.ne']
      rw [show (Q γ : ℂ) - 2 * z = 2 * w by dsimp [w]; ring,
        show 2 * w * (t : ℂ) / 2 ^ 2 = (t : ℂ) * w / 2 by ring]
      ring
    rw [hEq]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have hcNorm : ‖complexDenom γ (t : ℂ)‖ = realDenom γ t := by
        rw [show complexDenom γ (t : ℂ) = (realDenom γ t : ℂ) by simp [complexDenom, realDenom],
          Complex.norm_real, Real.norm_of_nonneg hdenPos.le]
      rw [norm_div, norm_mul, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_exp,
        Complex.neg_re, Complex.ofReal_re, hcNorm, norm_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_of_nonneg hdenPos.le, Real.norm_of_nonneg ht0.le, div_le_iff₀ (mul_pos hdenPos ht0)]
      exact mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_left ht hdenPos.le) (by positivity)
    · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hdenPos.le, div_le_iff₀ hdenPos]
      have hre : |(w * (t / 2)).re| = |w.re| * (t / 2) := by
        rw [show (w * (t / 2)).re = w.re * (t / 2) by simp, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
      have hprod : ‖Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))‖ ≤ Real.exp (|w.re| * t) := by
        rw [norm_mul]
        exact (mul_le_mul (hre ▸ complex_sinh_norm_le_exp_abs_re _)
          (hre ▸ complex_cosh_norm_le_exp_abs_re _) (norm_nonneg _) (Real.exp_pos _).le).trans_eq
          (by rw [← Real.exp_add]; congr 1; ring)
      refine hprod.trans ?_
      have hfac : (tailConst γ)⁻¹ * Real.exp (-δ * t) * (tailConst γ * Real.exp (Q γ / 2 * t)) =
          Real.exp (|w.re| * t) := by
        calc _ = ((tailConst γ)⁻¹ * tailConst γ) * (Real.exp (-δ * t) * Real.exp (Q γ / 2 * t)) := by ring
          _ = Real.exp (|w.re| * t) := by
              rw [inv_mul_cancel₀ hK.ne', one_mul, ← Real.exp_add]
              congr 1; dsimp [δ]; ring
      simpa [w, δ] using hfac.symm.trans_le (mul_le_mul_of_nonneg_left (realDenom_ge_tail_exp hγ ht) (by positivity))
  have deriv_upsilonLogIntegrand {t : ℝ} (ht : 0 < t) (z : ℂ) : deriv (fun z : ℂ => upsilonLogIntegrand γ z t) z = upsilonLogIntegrandDeriv γ z t := by
    have hD : (realDenom γ t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (realDenom_pos hγ ht).ne'
    have hS₁ : Complex.sinh ((t : ℂ) * (γ : ℂ) / 4) ≠ 0 := by
      rw [show (t : ℂ) * (γ : ℂ) / 4 = ((t * γ / 4 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sinh]
      exact Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (by positivity)).ne'
    have hS₂ : Complex.sinh ((t : ℂ) / (γ : ℂ)) ≠ 0 := by
      rw [show (t : ℂ) / (γ : ℂ) = ((t / γ : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_sinh]
      exact Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (div_pos ht hγ)).ne'
    simp (disch := fun_prop) [upsilonLogIntegrand, upsilonLogIntegrandDeriv,
      zDerivNum, zDerivNumComplex, realDenom, complexDenom, deriv_csinh, deriv_cexp]
    field_simp [hD, Complex.ofReal_ne_zero.mpr ht.ne', mod_cast hγ.ne', hS₁, hS₂]; ring_nf
  intro z₀ ⟨hz₀, hzQ⟩
  let r := min z₀.re (Q γ - z₀.re) / 2
  let w₀ := (Q γ / 2 : ℂ) - z₀
  let W := ‖w₀‖ + r
  let B := (tailConst γ)⁻¹
  have hr : 0 < r := by positivity
  have hB_nn : 0 ≤ B := (inv_pos.mpr (tailConst_pos hγ)).le
  obtain ⟨C, hC, hTaylor⟩ := exists_zDerivNum_taylor_bound w₀ r
  let A := 4 * C * Real.exp 1 + 2 * W
  let bound (t : ℝ) := A * Real.exp (-t) + B * Real.exp (-r * t)
  have hparam_bound : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      ∀ z ∈ Metric.ball z₀ r, ‖upsilonLogIntegrandDeriv γ z t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t) z hz
    have hdist : ‖(Q γ / 2 : ℂ) - z - w₀‖ < r := by
      rw [show (Q γ / 2 : ℂ) - z - w₀ = z₀ - z by dsimp [w₀]; ring, norm_sub_rev]
      simpa [dist_eq_norm] using Metric.mem_ball.mp hz
    by_cases ht1 : t ≤ 1
    · have hTay : ‖zDerivNum γ ((Q γ / 2 : ℂ) - z) t‖ ≤ C * t ^ 3 :=
        hTaylor _ (Metric.mem_closedBall.mpr (by rw [dist_eq_norm]; exact hdist.le)) t ⟨ht.le, ht1⟩
      have hdenPos := realDenom_pos hγ ht
      have hle4C : ‖upsilonLogIntegrandDeriv γ z t‖ ≤ 4 * C := by
        rw [upsilonLogIntegrandDeriv, norm_div, norm_mul, Complex.norm_real, Complex.norm_real,
          Real.norm_of_nonneg hdenPos.le, Real.norm_of_nonneg ht.le, div_le_iff₀ (mul_pos hdenPos ht)]
        have hq := mul_le_mul_of_nonneg_right (realDenom_ge_quadratic hγ ht) ht.le
        exact hTay.trans (by nlinarith [mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 4 * C)])
      have hexp : 1 ≤ Real.exp 1 * Real.exp (-t) := by
        rw [← Real.exp_add, show 1 + -t = 1 - t by ring]; exact Real.one_le_exp (by linarith)
      refine hle4C.trans (le_trans ?_ (le_add_of_nonneg_right (mul_nonneg hB_nn (Real.exp_pos _).le)))
      dsimp [A]
      nlinarith [mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 4 * C),
        mul_nonneg (by positivity : 0 ≤ W) (Real.exp_pos (-t)).le]
    · have ht' : 1 ≤ t := le_of_not_ge ht1
      have hre : |z.re - z₀.re| < r :=
        (Complex.abs_re_le_norm (z - z₀)).trans_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hz)
      have hz_b : r < z.re ∧ z.re < Q γ - r := by grind
      have hw_m : r ≤ Q γ / 2 - |Q γ / 2 - z.re| := by grind
      have hw_n : ‖(Q γ / 2 : ℂ) - z‖ ≤ W := by
        calc ‖(Q γ / 2 : ℂ) - z‖ = ‖w₀ + ((Q γ / 2 : ℂ) - z - w₀)‖ := by congr 1; ring
          _ ≤ ‖w₀‖ + ‖(Q γ / 2 : ℂ) - z - w₀‖ := norm_add_le _ _
          _ ≤ W := by dsimp [W]; linarith [hdist]
      refine (upsilonLogIntegrandDeriv_norm_le_tail z (lt_trans hr hz_b.1)
        (by linarith [hz_b.2]) ht').trans (add_le_add ?_ ?_)
      · exact mul_le_mul_of_nonneg_right (by dsimp [A]; nlinarith [mul_nonneg hC (Real.exp_pos 1).le])
          (Real.exp_pos _).le
      · exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hB_nn
  have hBound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    have h1 : IntegrableOn (fun t => A * Real.exp (-t)) (Ioi 0) := by
      change Integrable (fun t => A * Real.exp (-t)) (volume.restrict (Ioi 0))
      simpa [mul_comm] using (exp_neg_integrableOn_Ioi 0 (b := 1) zero_lt_one).const_mul A
    have h2 : IntegrableOn (fun t => B * Real.exp (-r * t)) (Ioi 0) := by
      change Integrable (fun t => B * Real.exp (-r * t)) (volume.restrict (Ioi 0))
      simpa [mul_comm] using (exp_neg_integrableOn_Ioi 0 (b := r) hr).const_mul B
    exact h1.add h2
  have hF'_meas : AEStronglyMeasurable (upsilonLogIntegrandDeriv γ z₀) (volume.restrict (Ioi 0)) :=
    (((by fun_prop [zDerivNum, zDerivNumComplex, complexDenom] :
      Measurable fun t : ℝ => zDerivNum γ ((Q γ / 2 : ℂ) - z₀) t).div
      (by fun_prop [realDenom] : Measurable fun t : ℝ => (realDenom γ t : ℂ) * (t : ℂ))).aestronglyMeasurable).restrict
  obtain ⟨_, hhas⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := upsilonLogIntegrandDeriv γ) (s := Metric.ball z₀ r) (Metric.ball_mem_nhds z₀ hr)
    (Eventually.of_forall fun z => (upsilonLogIntegrand_aestronglyMeasurable γ z).restrict)
    (upsilonLogIntegrand_integrableOn hγ hγ2 z₀ hz₀ hzQ) hF'_meas hparam_bound hBound_int
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht z _ => by
      simpa [deriv_upsilonLogIntegrand ht z] using
        (by fun_prop [upsilonLogIntegrand] : DifferentiableAt ℂ (fun z => upsilonLogIntegrand γ z t) z).hasDerivAt)
  exact hhas.differentiableAt.differentiableWithinAt

end

end DOZZ.Proofs

end
