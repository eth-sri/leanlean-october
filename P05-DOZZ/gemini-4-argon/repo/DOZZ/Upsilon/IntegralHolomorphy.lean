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

private lemma deriv_real_restrict (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    deriv (fun t : ℝ => F (t : ℂ)) = fun t : ℝ => deriv F (t : ℂ) := by
  funext t
  exact (hF t).hasDerivAt.comp_ofReal.deriv

private def zDerivNumComplex (γ : ℝ) (w t : ℂ) : ℂ :=
  -2 * w * Complex.exp (-t) * complexDenom γ t +
    t * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))

private def zDerivNum (γ : ℝ) (w : ℂ) (t : ℝ) : ℂ :=
  zDerivNumComplex γ w (t : ℂ)

private def zDerivNumJoint (γ : ℝ) (p : ℂ × ℝ) : ℂ :=
  zDerivNum γ p.1 p.2














private def upsilonLogIntegrandDeriv (γ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  zDerivNum γ ((Q γ / 2 : ℂ) - z) t /
    ((realDenom γ t : ℂ) * (t : ℂ))






/-- The logarithm given by the convergent integral is holomorphic on its defining strip. -/
theorem upsilonLog_differentiableOn {γ : ℝ}
    (hγ : 0 < γ) (_hγ2 : γ < 2) :
    DifferentiableOn ℂ (fun z => upsilonLog γ z)
      {z | 0 < z.re ∧ z.re < Q γ} := by
  have zDerivNumContDiff w : ContDiff ℝ 3 (zDerivNum γ w) := by
    change ContDiff ℝ 3 (fun t : ℝ => zDerivNumComplex γ w (t : ℂ))
    exact (show ContDiff ℂ 3 (zDerivNumComplex γ w) by fun_prop [zDerivNumComplex, complexDenom]).restrict_scalars ℝ |>.comp Complex.ofRealCLM.contDiff
  have zDerivNumComplex_deriv_eq (γ : ℝ) w : deriv (zDerivNumComplex γ w) = fun t => -2 * w * Complex.exp (-t) * ((γ : ℂ) / 4 * Complex.cosh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ)) + (γ : ℂ)⁻¹ * Complex.sinh (t * (γ : ℂ) / 4) * Complex.cosh (t / (γ : ℂ))) + 2 * w * Complex.exp (-t) * complexDenom γ t + Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) + t * w / 2 * (Complex.cosh (w * (t / 2)) ^ 2 + Complex.sinh (w * (t / 2)) ^ 2) := by
    funext t
    change deriv (fun t : ℂ =>
        -2 * w * Complex.exp (-t) *
            (Complex.sinh (t * (γ : ℂ) / 4) * Complex.sinh (t / (γ : ℂ))) +
          t * Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))) t = _
    simp (disch := fun_prop) [complexDenom, deriv_csinh, deriv_ccosh, deriv_cexp]
    ring_nf
  have upsilonLog_hasDerivAt (hγ2 : γ < 2) (z₀ : ℂ) (hz₀ : 0 < z₀.re) (hzQ : z₀.re < Q γ) : HasDerivAt (fun z : ℂ => upsilonLog γ z) (∫ t in Ioi (0 : ℝ), upsilonLogIntegrandDeriv γ z₀ t) z₀ := by
    have upsilonLogIntegrandDeriv_aestronglyMeasurable z : AEStronglyMeasurable (fun t : ℝ => upsilonLogIntegrandDeriv γ z t) volume := ((show Measurable (fun t => zDerivNum γ ((Q γ / 2 : ℂ) - z) t) by fun_prop [zDerivNum, zDerivNumComplex, complexDenom]).div (by fun_prop [realDenom])).aestronglyMeasurable
    have upsilonLogIntegrandDeriv_norm_le_tail (z : ℂ) (hz0 : 0 < z.re) (hzQ : z.re < Q γ) {t} (ht : 1 ≤ t) : ‖upsilonLogIntegrandDeriv γ z t‖ ≤ 2 * ‖(Q γ / 2 : ℂ) - z‖ * Real.exp (-t) + (tailConst γ)⁻¹ * Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) := by
      let w := (Q γ / 2 : ℂ) - z
      let δ := Q γ / 2 - |w.re|
      have hdenPos := realDenom_pos hγ (by linarith : 0 < t)
      have hdenLower := realDenom_ge_tail_exp hγ ht
      have hK := tailConst_pos hγ
      have hlinear :
          ‖-2 * w * Complex.exp (-(t : ℂ)) * complexDenom γ (t : ℂ) /
              ((realDenom γ t : ℂ) * (t : ℂ))‖ ≤
            2 * ‖w‖ * Real.exp (-t) := by
        calc
          _ = (2 * ‖w‖ * Real.exp (-t) * realDenom γ t) /
              (realDenom γ t * t) := by
                rw [norm_div, (show ‖(realDenom γ t : ℂ) * (t : ℂ)‖ = realDenom γ t * t by rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hdenPos, abs_of_pos (by linarith : 0 < t)])]
                simp [(show ‖complexDenom γ (t : ℂ)‖ = realDenom γ t by rw [(show complexDenom γ (t : ℂ) = (realDenom γ t : ℂ) by simp [complexDenom, realDenom]), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos]), (show ‖Complex.exp (-(t : ℂ))‖ = Real.exp (-t) by simp [Complex.norm_exp])]
          _ ≤ 2 * ‖w‖ * Real.exp (-t) := by
            rw [div_le_iff₀ (mul_pos hdenPos (show 0 < t by linarith))]
            exact mul_le_mul_of_nonneg_left (by simpa using mul_le_mul_of_nonneg_left ht hdenPos.le) (by positivity)
      have hnonlinear :
          ‖(Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))) /
              (realDenom γ t : ℂ)‖ ≤
            (tailConst γ)⁻¹ * Real.exp (-δ * t) := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos]
        have hSinh : ‖Complex.sinh (w * (t / 2))‖ ≤ Real.exp (|w.re| * (t / 2)) := by
          calc
            _ ≤ Real.exp |(w * (t / 2)).re| := complex_sinh_norm_le_exp_abs_re _
            _ = Real.exp (|w.re| * (t / 2)) := by
              rw [(show (w * (t / 2)).re = w.re * (t / 2) by simp), abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
        have hCosh : ‖Complex.cosh (w * (t / 2))‖ ≤ Real.exp (|w.re| * (t / 2)) := by
          calc
            _ ≤ Real.exp |(w * (t / 2)).re| := complex_cosh_norm_le_exp_abs_re _
            _ = Real.exp (|w.re| * (t / 2)) := by
              rw [(show (w * (t / 2)).re = w.re * (t / 2) by simp), abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
        have hprod :
            ‖Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))‖ ≤
              Real.exp (|w.re| * t) := by
          calc
            _ = ‖Complex.sinh (w * (t / 2))‖ * ‖Complex.cosh (w * (t / 2))‖ := norm_mul _ _
            _ ≤ Real.exp (|w.re| * (t / 2)) * Real.exp (|w.re| * (t / 2)) :=
              mul_le_mul hSinh hCosh (norm_nonneg _) (Real.exp_pos _).le
            _ = Real.exp (|w.re| * t) := by
              rw [← Real.exp_add]
              congr 1
              ring
        have hden :
            (tailConst γ)⁻¹ * Real.exp (-δ * t) * realDenom γ t ≥
              Real.exp (|w.re| * t) := by
          have hfactor :
              (tailConst γ)⁻¹ * Real.exp (-δ * t) *
                  (tailConst γ * Real.exp (Q γ / 2 * t)) = Real.exp (|w.re| * t) := by
            calc
              _ = ((tailConst γ)⁻¹ * tailConst γ) *
                  (Real.exp (-δ * t) * Real.exp (Q γ / 2 * t)) := by ring
              _ = Real.exp (|w.re| * t) := by
                rw [inv_mul_cancel₀ hK.ne', ← Real.exp_add]
                rw [show -δ * t + Q γ / 2 * t = |w.re| * t by dsimp [δ]; ring]
                simp
          calc
            _ ≥ (tailConst γ)⁻¹ * Real.exp (-δ * t) *
                (tailConst γ * Real.exp (Q γ / 2 * t)) :=
                  mul_le_mul_of_nonneg_left hdenLower (by positivity)
            _ = _ := hfactor
        calc
          _ = ‖Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))‖ /
              realDenom γ t := rfl
          _ ≤ Real.exp (|w.re| * t) / realDenom γ t :=
            div_le_div_of_nonneg_right hprod hdenPos.le
          _ ≤ _ := ((div_le_iff₀ hdenPos).2 hden)
      have hEq : upsilonLogIntegrandDeriv γ z t =
          (-2 * w * Complex.exp (-(t : ℂ)) * complexDenom γ (t : ℂ) /
              ((realDenom γ t : ℂ) * (t : ℂ))) +
            (Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) /
              (realDenom γ t : ℂ)) := by
        rw [upsilonLogIntegrandDeriv, zDerivNum, zDerivNumComplex]
        field_simp [(Complex.ofReal_ne_zero.mpr (by linarith) : (t : ℂ) ≠ 0), (Complex.ofReal_ne_zero.mpr hdenPos.ne')]
        rw [(show (Q γ : ℂ) - 2 * z = 2 * w by dsimp [w]; ring)]
        rw [(show (2 * w) * (t : ℂ) / 2 ^ 2 = (t : ℂ) * w / 2 by ring)]
        ring
      rw [hEq]
      calc
        _ ≤ 2 * ‖w‖ * Real.exp (-t) +
            (tailConst γ)⁻¹ * Real.exp (-δ * t) := by
              exact (norm_add_le (-2 * w * Complex.exp (-(t : ℂ)) * complexDenom γ (t : ℂ) / ((realDenom γ t : ℂ) * (t : ℂ))) (Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) / (realDenom γ t : ℂ))).trans (add_le_add hlinear hnonlinear)
        _ = _ := by simp [w, δ]
    have upsilonLogIntegrandDeriv_norm_le_of_taylor z C (hC : 0 ≤ C) {t} (ht : 0 < t) (_ht1 : t ≤ 1) (hTaylor : ‖zDerivNum γ ((Q γ / 2 : ℂ) - z) t‖ ≤ C * t ^ 3) : ‖upsilonLogIntegrandDeriv γ z t‖ ≤ 4 * C := by
      have hdenPos := realDenom_pos hγ ht
      have hdenTLower : t ^ 3 / 4 ≤ realDenom γ t * t := by
        calc
          t ^ 3 / 4 = (t ^ 2 / 4) * t := by ring
          _ ≤ realDenom γ t * t := mul_le_mul_of_nonneg_right (realDenom_ge_quadratic hγ ht) ht.le
      rw [upsilonLogIntegrandDeriv, norm_div, (show ‖(realDenom γ t : ℂ) * (t : ℂ)‖ = realDenom γ t * t by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]), div_le_iff₀ (mul_pos hdenPos ht)]
      exact le_trans hTaylor (by linarith only [(mul_le_mul_of_nonneg_left hdenTLower (mul_nonneg (by norm_num) hC : 0 ≤ 4 * C))])
    have deriv_upsilonLogIntegrand {t} (ht : 0 < t) (z : ℂ) : deriv (fun z : ℂ => upsilonLogIntegrand γ z t) z = upsilonLogIntegrandDeriv γ z t := by
      simp (disch := fun_prop) [upsilonLogIntegrand, upsilonLogIntegrandDeriv,
        zDerivNum, zDerivNumComplex, realDenom, complexDenom,
        deriv_csinh, deriv_cexp]
      field_simp [(Complex.ofReal_ne_zero.mpr (realDenom_pos hγ ht).ne'), (Complex.ofReal_ne_zero.mpr ht.ne'), (show (γ : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt hγ)), (show Complex.sinh ((t : ℂ) * (γ : ℂ) / 4) ≠ 0 by rw [show (t : ℂ) * (γ : ℂ) / 4 = ((t * γ / 4 : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_sinh]; exact Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (by positivity)).ne'), (show Complex.sinh ((t : ℂ) / (γ : ℂ)) ≠ 0 by rw [show (t : ℂ) / (γ : ℂ) = ((t / γ : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_sinh]; exact Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (div_pos ht hγ)).ne')]
      ring_nf
    have exists_zDerivNum_taylor_bound w₀ r : ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.closedBall w₀ r, ∀ t ∈ Icc 0 1, ‖zDerivNum γ w t‖ ≤ C * t ^ 3 := by
      have zDerivNum_taylorWithinEval_zero w t : taylorWithinEval (zDerivNum γ w) 2 (Icc 0 1) 0 t = 0 := by
        have zDerivNum_iteratedDerivWithin_two_zero : iteratedDerivWithin 2 (zDerivNum γ w) (Icc 0 1) 0 = 0 := by
          have zDerivNum_iteratedDeriv_two_zero : iteratedDeriv 2 (zDerivNum γ w) 0 = 0 := by
            change iteratedDeriv 2 (fun t : ℝ => zDerivNumComplex γ w (t : ℂ)) 0 = 0
            rw [iteratedDeriv_succ]
            rw [(show iteratedDeriv 1 (fun t : ℝ => zDerivNumComplex γ w (t : ℂ)) = fun t : ℝ => deriv (zDerivNumComplex γ w) (t : ℂ) by simpa [iteratedDeriv_succ] using deriv_real_restrict _ ((by fun_prop [zDerivNumComplex, complexDenom] : ContDiff ℂ 1 (zDerivNumComplex γ w)).differentiable (by norm_num)))]
            calc
              deriv (fun t : ℝ => deriv (zDerivNumComplex γ w) (t : ℂ)) 0 =
                  deriv (deriv (zDerivNumComplex γ w)) 0 := (((show Differentiable ℂ (deriv (zDerivNumComplex γ w)) by simpa [iteratedDeriv_succ] using ((by fun_prop [zDerivNumComplex, complexDenom] : ContDiff ℂ 3 (zDerivNumComplex γ w)).of_le (by norm_num)).differentiable_iteratedDeriv' 1) (0 : ℂ)).hasDerivAt.comp_ofReal.deriv)
              _ = iteratedDeriv 2 (zDerivNumComplex γ w) 0 := by
                rw [iteratedDeriv_succ]
                simp
              _ = 0 := (by rw [iteratedDeriv_succ, show iteratedDeriv 1 (zDerivNumComplex γ w) = deriv (zDerivNumComplex γ w) by simp, zDerivNumComplex_deriv_eq]; simp (disch := fun_prop) [complexDenom, deriv_csinh, deriv_ccosh, deriv_cexp]; field_simp [(by exact_mod_cast (ne_of_gt hγ))]; ring)
          rw [(iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) ((zDerivNumContDiff w).contDiffAt.of_le (by norm_num) : ContDiffAt ℝ 2 (zDerivNum γ w) 0) (by simp))]
          exact zDerivNum_iteratedDeriv_two_zero
        rw [taylor_within_apply]
        simp [Finset.sum_range_succ, (by simpa using (show zDerivNum γ w 0 = 0 by simp [zDerivNum, zDerivNumComplex, complexDenom])), ((show iteratedDerivWithin 1 (zDerivNum γ w) (Icc 0 1) 0 = 0 by rw [(iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) ((zDerivNumContDiff w).contDiffAt.of_le (by norm_num) : ContDiffAt ℝ 1 (zDerivNum γ w) 0) (by simp))]; simpa [iteratedDeriv_succ] using (by change deriv (fun t : ℝ => zDerivNumComplex γ w (t : ℂ)) 0 = 0; rw [deriv_real_restrict _ ((by fun_prop [zDerivNumComplex, complexDenom] : ContDiff ℂ 1 (zDerivNumComplex γ w)).differentiable (by norm_num))]; exact (by rw [zDerivNumComplex_deriv_eq]; simp [complexDenom])))), (zDerivNum_iteratedDerivWithin_two_zero)]
      have zDerivNum_third_continuous : Continuous (fun p : ℂ × ℝ => iteratedDeriv 3 (zDerivNum γ p.1) p.2) := by
        have zDerivNumJoint_contDiff : ContDiff ℝ 3 (zDerivNumJoint γ) := by
          change ContDiff ℝ 3 ((fun q : ℂ × ℂ => zDerivNumComplex γ q.1 q.2) ∘
            fun p : ℂ × ℝ => (p.1, (p.2 : ℂ)))
          exact ((show ContDiff ℂ 3 (fun q : ℂ × ℂ => zDerivNumComplex γ q.1 q.2) by fun_prop [zDerivNumComplex, complexDenom]).restrict_scalars ℝ).comp (contDiff_fst.prodMk (Complex.ofRealCLM.contDiff.comp contDiff_snd))
        have hEq : (fun p : ℂ × ℝ =>
            iteratedDeriv 3 (zDerivNum γ p.1) p.2) =
          (fun p =>
            iteratedFDeriv ℝ 3 (zDerivNumJoint γ) p
              (fun _ : Fin 3 => (0, (1 : ℝ)))) := by
          funext p
          let line : ℝ → ℂ × ℝ := fun t => (p.1, t)
          have hlineD : deriv line = fun _ => (0, (1 : ℝ)) := by
            funext t
            exact ((hasDerivAt_const t p.1).prodMk (hasDerivAt_id t)).deriv
          have hline3 : iteratedDeriv 3 line p.2 = 0 := by
            rw [iteratedDeriv_succ]
            rw [show iteratedDeriv 2 line = fun _ => 0 by
              funext t
              rw [iteratedDeriv_succ, show iteratedDeriv 1 line = deriv line by simp, hlineD]
              simp]
            simp
          have hcomp := iteratedDeriv_vcomp_three
            (hg := zDerivNumJoint_contDiff.contDiffAt)
            (hf := (by fun_prop : ContDiffAt ℝ 3 line p.2))
          rw [(show iteratedDeriv 2 line p.2 = 0 by rw [iteratedDeriv_succ, show iteratedDeriv 1 line = deriv line by simp, hlineD]; simp), hline3] at hcomp
          simp only [line, hlineD] at hcomp
          rw [(show iteratedFDeriv ℝ 2 (zDerivNumJoint γ) p ![0, (0, (1 : ℝ))] = 0 by apply ContinuousMultilinearMap.map_coord_zero _ 0; simp), (show iteratedFDeriv ℝ 2 (zDerivNumJoint γ) p ![(0, (1 : ℝ)), 0] = 0 by apply ContinuousMultilinearMap.map_coord_zero _ 1; simp)] at hcomp
          simpa [line, Function.comp_def, zDerivNumJoint] using hcomp
        rw [hEq]
        fun_prop
      obtain ⟨C₀, hC₀⟩ := (show IsCompact (Metric.closedBall w₀ r ×ˢ Icc 0 1 : Set (ℂ × ℝ)) by change IsCompact (Metric.closedBall w₀ r ×ˢ Icc (0 : ℝ) 1); exact IsCompact.prod (isCompact_closedBall w₀ r) isCompact_Icc).bddAbove_image ((zDerivNum_third_continuous).norm.continuousOn)
      let C := max C₀ 0
      refine ⟨C, le_max_right _ _, ?_⟩
      intro w hw t ht
      have hTaylor := taylor_mean_remainder_bound
        (f := zDerivNum γ w) (a := 0) (b := 1) (C := C) (x := t) (n := 2)
        (by norm_num) (zDerivNumContDiff w).contDiffOn
        ht (by intro y hy; rw [(iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) ((zDerivNumContDiff w).contDiffAt) hy)]; apply le_trans _ (le_max_left C₀ 0); exact hC₀ ⟨(w, y), ⟨hw, hy⟩, rfl⟩)
      rw [zDerivNum_taylorWithinEval_zero w t] at hTaylor
      norm_num at hTaylor
      linarith only [hTaylor, (mul_nonneg (le_max_right _ _) (pow_nonneg ht.1 _) : 0 ≤ C * t ^ 3)]
    let margin := min z₀.re (Q γ - z₀.re)
    let r := margin / 2
    let q := (Q γ / 2 : ℂ)
    let w₀ := q - z₀
    let W := ‖w₀‖ + r
    let B := (tailConst γ)⁻¹
    have hr : 0 < r := by dsimp [r]; positivity
    have hB_nonneg : 0 ≤ B := by
      dsimp [B]
      exact le_of_lt (inv_pos.mpr (tailConst_pos hγ))
    obtain ⟨C, hC, hTaylor⟩ := exists_zDerivNum_taylor_bound w₀ r
    let A := 4 * C * Real.exp 1 + 2 * W
    let bound : ℝ → ℝ := fun t => A * Real.exp (-t) + B * Real.exp (-r * t)
    have hz_near (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
        |z.re - z₀.re| < r := by
      have hre := (Complex.abs_re_le_norm (z - z₀)).trans_lt (by
        simpa [dist_eq_norm] using (Metric.mem_ball.mp hz))
      simpa [Complex.sub_re] using hre
    have hz_real_bounds (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
        r < z.re ∧ z.re < Q γ - r := by
      have hc' := abs_lt.mp (hz_near z hz)
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
    have hw_norm_bound z (hz : z ∈ Metric.ball z₀ r) :
        ‖(Q γ / 2 : ℂ) - z‖ ≤ W := by
      have := Metric.mem_ball.mp hz
      have hdiff : dist ((Q γ / 2 : ℂ) - z) w₀ = dist z z₀ := by
        rw [dist_eq_norm, dist_eq_norm]
        rw [(show ((Q γ / 2 : ℂ) - z) - w₀ = z₀ - z by dsimp [w₀]; ring)]
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
    have hTaylor_local {z} (hz : z ∈ Metric.ball z₀ r)
        {t} (ht : t ∈ Icc 0 1) :
        ‖zDerivNum γ ((Q γ / 2 : ℂ) - z) t‖ ≤ C * t ^ 3 := by
      apply hTaylor
      · have hdist : dist ((Q γ / 2 : ℂ) - z) w₀ ≤ r := by
          rw [dist_eq_norm]
          rw [(show ((Q γ / 2 : ℂ) - z) - w₀ = z₀ - z by dsimp [w₀]; ring)]
          simpa [dist_eq_norm, norm_sub_rev] using (Metric.mem_ball.mp hz).le
        exact Metric.mem_closedBall.mpr hdist
      · exact ht
    have hparam_bound : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
        ∀ z ∈ Metric.ball z₀ r,
          ‖upsilonLogIntegrandDeriv γ z t‖ ≤ bound t := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro z hz
      by_cases ht1 : t ≤ 1
      · have hTaylor' := hTaylor_local hz ⟨le_of_lt ht, ht1⟩
        have hcoeff : 4 * C ≤ A * Real.exp (-t) := by
          dsimp [A]
          have h := mul_le_mul_of_nonneg_left (Real.one_le_exp_iff.mpr (by linarith) : 1 ≤ Real.exp (1 - t)) (by positivity : 0 ≤ 4 * C)
          rw [(show Real.exp (1 - t) = Real.exp 1 * Real.exp (-t) by rw [← Real.exp_add]; congr 1)] at h
          linarith only [h, mul_nonneg (show 0 ≤ W by dsimp [W]; positivity) (Real.exp_pos (-t)).le]
        calc
          _ ≤ 4 * C := (upsilonLogIntegrandDeriv_norm_le_of_taylor z C hC ht ht1 hTaylor')
          _ ≤ A * Real.exp (-t) := hcoeff
          _ ≤ bound t := by
            dsimp [bound]
            exact le_add_of_nonneg_right (mul_nonneg hB_nonneg (Real.exp_pos _).le)
      · have ht' : 1 ≤ t := le_of_not_ge ht1
        obtain ⟨hzlow, hzhigh⟩ := hz_real_bounds z hz
        have hδ : r ≤ Q γ / 2 - |Q γ / 2 - z.re| := by
          have := hw_re_margin z hz
          linarith
        have hfirst :
            2 * ‖(Q γ / 2 : ℂ) - z‖ * Real.exp (-t) ≤ A * Real.exp (-t) :=
          mul_le_mul_of_nonneg_right (by
            calc
              2 * ‖(Q γ / 2 : ℂ) - z‖ ≤ 2 * W := by
                exact mul_le_mul_of_nonneg_left (hw_norm_bound z hz) (by norm_num)
              _ ≤ A := (by dsimp [A]; linarith only [mul_nonneg hC (Real.exp_pos 1).le])) (Real.exp_pos _).le
        simpa [bound, B] using (upsilonLogIntegrandDeriv_norm_le_tail z (lt_trans hr hzlow) (lt_of_lt_of_le hzhigh (by linarith [hr])) ht').trans (add_le_add hfirst (by apply mul_le_mul_of_nonneg_left _ hB_nonneg; apply Real.exp_le_exp.mpr; linarith only [(mul_le_mul_of_nonneg_right hδ (show 0 ≤ t by linarith))]))
    obtain ⟨_, hhas⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := Metric.ball z₀ r) (Metric.ball_mem_nhds z₀ hr) (by filter_upwards [] with z; exact (upsilonLogIntegrand_aestronglyMeasurable γ z).restrict) (upsilonLogIntegrand_integrableOn hγ hγ2 z₀ hz₀ hzQ) ((upsilonLogIntegrandDeriv_aestronglyMeasurable z₀).restrict) hparam_bound (by change IntegrableOn (fun t => A * Real.exp (-t) + B * Real.exp (-r * t)) (Ioi (0 : ℝ)); exact (show IntegrableOn (fun t : ℝ => A * Real.exp (-t)) (Ioi (0 : ℝ)) by change Integrable (fun t : ℝ => A * Real.exp (-t)) (volume.restrict (Ioi (0 : ℝ))); simpa [mul_comm] using (exp_neg_integrableOn_Ioi 0 (b := 1) (by norm_num)).const_mul A).add (by change Integrable (fun t : ℝ => B * Real.exp (-r * t)) (volume.restrict (Ioi (0 : ℝ))); simpa [mul_comm] using (exp_neg_integrableOn_Ioi 0 (b := r) hr).const_mul B)) (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; intro z hz; simpa [deriv_upsilonLogIntegrand ht z] using (show DifferentiableAt ℂ (fun z => upsilonLogIntegrand γ z t) z by fun_prop [upsilonLogIntegrand]).hasDerivAt)
    simpa [upsilonLog] using hhas
  intro z hz
  exact (upsilonLog_hasDerivAt _hγ2 z hz.1 hz.2).differentiableAt.differentiableWithinAt

end

end DOZZ.Proofs

end
