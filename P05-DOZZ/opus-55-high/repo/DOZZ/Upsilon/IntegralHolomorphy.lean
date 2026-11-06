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
section
variable (γ : ℝ)

private lemma zDerivNumJoint_contDiff :
    ContDiff ℝ 3 (zDerivNumJoint γ) := by
  have hF : ContDiff ℂ 3 (fun q : ℂ × ℂ => zDerivNumComplex γ q.1 q.2) := by
    fun_prop [zDerivNumComplex, complexDenom]
  have hF' :=
    hF.restrict_scalars ℝ
  have hPair : ContDiff ℝ 3 (fun p : ℂ × ℝ => (p.1, (p.2 : ℂ))) := by
    exact contDiff_fst.prodMk (Complex.ofRealCLM.contDiff.comp contDiff_snd)
  change ContDiff ℝ 3 ((fun q => zDerivNumComplex γ q.1 q.2) ∘
    fun p : ℂ × ℝ => (p.1, (p.2 : ℂ)))
  fun_prop

private lemma zDerivNum_third_continuous :
    Continuous (fun p : ℂ × ℝ =>
      iteratedDeriv 3 (zDerivNum γ p.1) p.2) := by
  have hJ := zDerivNumJoint_contDiff γ
  have hF : Continuous (fun p : ℂ × ℝ =>
      iteratedFDeriv ℝ 3 (zDerivNumJoint γ) p) :=
    by fun_prop
  have hEq : (fun p : ℂ × ℝ =>
      iteratedDeriv 3 (zDerivNum γ p.1) p.2) =
    (fun p : ℂ × ℝ =>
      iteratedFDeriv ℝ 3 (zDerivNumJoint γ) p
        (fun _ : Fin 3 => (0, (1 : ℝ)))) := by
    funext p
    let line : ℝ → ℂ × ℝ := fun t => (p.1, t)
    have hline : HasDerivAt line (0, (1 : ℝ)) p.2 := by
      simpa [line] using
        (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have hlineD : deriv line = fun _ => (0, (1 : ℝ)) := by
      funext t
      exact ((hasDerivAt_const t p.1).prodMk (hasDerivAt_id t)).deriv
    have hline2 : iteratedDeriv 2 line p.2 = 0 := by
      rw [iteratedDeriv_succ]
      simp_all
    have hline3 : iteratedDeriv 3 line p.2 = 0 := by
      rw [iteratedDeriv_succ]
      rw [show iteratedDeriv 2 line = fun _ => 0 by
        funext t
        rw [iteratedDeriv_succ]
        simp_all]
      simp
    have hcomp := iteratedDeriv_vcomp_three
      (hg := hJ.contDiffAt)
      (hf := (by fun_prop : ContDiffAt ℝ 3 line p.2))
    rw [hline2, hline3] at hcomp
    have hcross₁ :
        iteratedFDeriv ℝ 2 (zDerivNumJoint γ) p ![0, (0, (1 : ℝ))] = 0 := by
      apply ContinuousMultilinearMap.map_coord_zero _ 0
      simp
    have hcross₂ :
        iteratedFDeriv ℝ 2 (zDerivNumJoint γ) p ![(0, (1 : ℝ)), 0] = 0 := by
      apply ContinuousMultilinearMap.map_coord_zero _ 1
      simp
    simp only [line, hlineD] at hcomp
    rw [hcross₁, hcross₂] at hcomp
    simpa [line, Function.comp_def, zDerivNumJoint] using hcomp
  rw [hEq]
  fun_prop
section
variable (w : ℂ)

private lemma zDerivNumComplex_deriv_eq :
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
          (Complex.sinh _ * Complex.sinh _) +
        t * Complex.sinh _ * Complex.cosh _) t = _
  simp (disch := fun_prop) [complexDenom, deriv_csinh, deriv_ccosh, deriv_cexp]
  ring_nf

private lemma zDerivNumComplex_deriv_zero :
    deriv (zDerivNumComplex γ w) 0 = 0 := by
  rw [zDerivNumComplex_deriv_eq]
  simp [complexDenom]

end

end

private lemma zDerivNumComplex_iteratedDeriv_two_zero {γ : ℝ} (hγ : 0 < γ) (w : ℂ) :
    iteratedDeriv 2 (zDerivNumComplex γ w) 0 = 0 := by
  rw [iteratedDeriv_succ, show iteratedDeriv 1 (zDerivNumComplex γ w) = deriv (zDerivNumComplex γ w) by simp, zDerivNumComplex_deriv_eq]
  simp (disch := fun_prop) [complexDenom, deriv_csinh, deriv_ccosh, deriv_cexp]
  have hγC : γ ≠ 0 := by positivity
  field_simp [hγC]
  ring
section
variable (γ : ℝ) (w : ℂ)

private lemma zDerivNumContDiff :
    ContDiff ℝ 3 (zDerivNum γ w) := by
  have hC : ContDiff ℂ 3 (zDerivNumComplex γ w) := by
    fun_prop [zDerivNumComplex, complexDenom]
  exact hC.restrict_scalars ℝ |>.comp Complex.ofRealCLM.contDiff

private lemma zDerivNum_zero : zDerivNum γ w 0 = 0 := by
  simp [zDerivNum, zDerivNumComplex, complexDenom]

private lemma zDerivNum_deriv_zero : deriv (zDerivNum γ w) 0 = 0 := by
  have hF : Differentiable ℂ (zDerivNumComplex γ w) :=
    (by fun_prop [zDerivNumComplex, complexDenom] : ContDiff ℂ 1 _).differentiable
      (by norm_num)
  change deriv (fun t : ℝ => zDerivNumComplex γ w (t : ℂ)) 0 = 0
  rw [deriv_real_restrict _ hF]
  exact zDerivNumComplex_deriv_zero γ w

end

private lemma zDerivNum_iteratedDeriv_two_zero {γ : ℝ} (hγ : 0 < γ) (w : ℂ) :
    iteratedDeriv 2 (zDerivNum γ w) 0 = 0 := by
  change iteratedDeriv 2 (fun t : ℝ => zDerivNumComplex γ w (t : ℂ)) 0 = 0
  rw [iteratedDeriv_succ]
  have hF : Differentiable ℂ (zDerivNumComplex γ w) :=
    (by fun_prop [zDerivNumComplex, complexDenom] : ContDiff ℂ 1 _).differentiable
      (by norm_num)
  have hfirst : iteratedDeriv 1 (fun t : ℝ => zDerivNumComplex γ w (t : ℂ)) =
      fun t : ℝ => deriv (zDerivNumComplex γ w) (t : ℂ) := by
    simpa [iteratedDeriv_succ] using deriv_real_restrict _ hF
  rw [hfirst]
  have hC2 : ContDiff ℂ 2 (zDerivNumComplex γ w) := by
    exact (by fun_prop [zDerivNumComplex, complexDenom] : ContDiff ℂ 3
      (zDerivNumComplex γ w)).of_le (by norm_num)
  have hF' : Differentiable ℂ (deriv (zDerivNumComplex γ w)) := by
    fun_prop
  calc
    deriv (fun t : ℝ => deriv _ (t : ℂ)) 0 =
        deriv _ 0 := ((hF' (0 : ℂ)).hasDerivAt.comp_ofReal.deriv)
    _ = iteratedDeriv 2 (zDerivNumComplex γ w) 0 := by
      rw [iteratedDeriv_succ]
      simp
    _ = 0 := zDerivNumComplex_iteratedDeriv_two_zero hγ w

private lemma zDerivNum_iteratedDerivWithin_one_zero (γ : ℝ) (w : ℂ) :
    iteratedDerivWithin 1 (zDerivNum γ w) (Icc 0 1) 0 = 0 := by
  have hf : ContDiffAt ℝ 1 (zDerivNum γ w) 0 :=
    (zDerivNumContDiff γ w).contDiffAt.of_le (by norm_num)
  have hEq := iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hf (by simp)
  rw [hEq]
  simpa [iteratedDeriv_succ] using zDerivNum_deriv_zero γ w
section
variable {γ : ℝ}
section
variable (hγ : 0 < γ)
include hγ
section
variable (w : ℂ)

private lemma zDerivNum_iteratedDerivWithin_two_zero : iteratedDerivWithin 2 (zDerivNum γ w) (Icc 0 1) 0 = 0 := by
  have hf : ContDiffAt ℝ 2 (zDerivNum γ w) 0 :=
    (zDerivNumContDiff γ w).contDiffAt.of_le (by norm_num)
  have hEq := iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)) hf (by simp)
  rw [hEq]
  exact zDerivNum_iteratedDeriv_two_zero hγ w

private lemma zDerivNum_taylorWithinEval_zero (t : ℝ) : taylorWithinEval (zDerivNum γ w) 2 (Icc 0 1) 0 t = 0 := by
  rw [taylor_within_apply]
  have h0 : iteratedDerivWithin 0 (zDerivNum γ w) (Icc 0 1) 0 = 0 := by
    simpa using zDerivNum_zero γ w
  simp [Finset.sum_range_succ, h0, (zDerivNum_iteratedDerivWithin_one_zero γ w), (zDerivNum_iteratedDerivWithin_two_zero hγ w)]

end

private lemma exists_zDerivNum_taylor_bound (w₀ : ℂ) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w ∈ Metric.closedBall w₀ r, ∀ t ∈ Icc 0 1,
      ‖zDerivNum γ w t‖ ≤ C * t ^ 3 := by
  let K : Set (ℂ × ℝ) := Metric.closedBall w₀ r ×ˢ Icc 0 1
  let derivativeNorm : ℂ × ℝ → ℝ := fun p =>
    ‖iteratedDeriv 3 (zDerivNum γ p.1) p.2‖
  have hK : IsCompact K := by
    exact IsCompact.prod (isCompact_closedBall w₀ r) isCompact_Icc
  have hcont : ContinuousOn derivativeNorm K :=
    (zDerivNum_third_continuous γ).norm.continuousOn
  obtain ⟨C₀, hC₀⟩ := hK.bddAbove_image hcont
  let C := max C₀ 0
  refine ⟨C, le_max_right .., ?_⟩
  intro w hw t ht
  have hderiv : ∀ y ∈ Icc 0 1,
      ‖iteratedDerivWithin 3 (zDerivNum γ w) (Icc 0 1) y‖ ≤ C := by
    intro y hy
    have hEq := iteratedDerivWithin_eq_iteratedDeriv
      (uniqueDiffOn_Icc (by norm_num))
      ((zDerivNumContDiff γ w).contDiffAt) hy
    rw [hEq]
    apply le_trans _ (le_max_left C₀ 0)
    have hp : (w, y) ∈ K := by tauto
    have himage : derivativeNorm (w, y) ∈ derivativeNorm '' K :=
      by grind
    exact hC₀ himage
  have hTaylor := taylor_mean_remainder_bound
   
    (by norm_num) (zDerivNumContDiff γ w).contDiffOn
    ht hderiv
  rw [zDerivNum_taylorWithinEval_zero hγ w t] at hTaylor
  norm_num at hTaylor
  have ht0 : 0 ≤ t := ht.1
  have hnonneg : 0 ≤ C * t ^ 3 := by positivity
  linarith only [hTaylor, hnonneg]

end

end

private def upsilonLogIntegrandDeriv (γ : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  zDerivNum γ ((Q γ / 2 : ℂ) - z) t /
    ((realDenom γ t : ℂ) * (t : ℂ))
section
variable {γ : ℝ}

private lemma deriv_upsilonLogIntegrand {t : ℝ}
    (hγ : 0 < γ) (ht : 0 < t) (z : ℂ) :
    deriv (fun z : ℂ => upsilonLogIntegrand γ z t) z =
      upsilonLogIntegrandDeriv γ z t := by
  have hD : (realDenom γ t : ℂ) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (realDenom_pos hγ ht).ne'
  have htC := Complex.ofReal_ne_zero.mpr ht.ne'
  have hγC : γ ≠ 0 := by positivity
  have hS₁ : Complex.sinh (t * γ / 4) ≠ 0 := by
    rw [show (t : ℂ) * (γ : ℂ) / 4 = ((t * γ / 4 : ℝ) : ℂ) by simp, ← Complex.ofReal_sinh]
    exact Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (by positivity)).ne'
  have hS₂ : Complex.sinh (t / γ) ≠ 0 := by
    rw [show (t : ℂ) / (γ : ℂ) = ((t / γ : ℝ) : ℂ) by simp, ← Complex.ofReal_sinh]
    exact Complex.ofReal_ne_zero.mpr (Real.sinh_pos_iff.2 (div_pos ht hγ)).ne'
  simp (disch := fun_prop) [upsilonLogIntegrand, upsilonLogIntegrandDeriv,
    zDerivNum, zDerivNumComplex, realDenom, complexDenom,
    deriv_csinh, deriv_cexp]
  grind
section
variable (hγ : 0 < γ) (z : ℂ)
include hγ

private lemma upsilonLogIntegrandDeriv_norm_le_of_taylor (C : ℝ) (hC : 0 ≤ C)
    {t : ℝ} (ht : 0 < t) (_ht1 : t ≤ 1)
    (hTaylor : ‖zDerivNum γ ((Q γ / 2 : ℂ) - z) t‖ ≤ C * t ^ 3) :
    ‖upsilonLogIntegrandDeriv γ z t‖ ≤ 4 * C := by
  have hdenPos := realDenom_pos hγ ht
  have hdenQuad := realDenom_ge_quadratic hγ ht
  have hdenTLower : t ^ 3 / 4 ≤ realDenom γ t * t := by
    nlinarith
  have hnormDen :
      ‖(realDenom γ t) * (t : ℂ)‖ = realDenom γ t * t := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
  rw [upsilonLogIntegrandDeriv, norm_div, hnormDen]
  rw [div_le_iff₀ (mul_pos hdenPos ht)]
  nlinarith

private lemma upsilonLogIntegrandDeriv_norm_le_tail (hz0 : 0 < z.re) (hzQ : z.re < Q γ) {t : ℝ} (ht : 1 ≤ t) :
    ‖upsilonLogIntegrandDeriv γ z t‖ ≤
      2 * ‖(Q γ / 2 : ℂ) - z‖ * Real.exp (-t) +
        (tailConst γ)⁻¹ * Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) := by
  let w := (Q γ / 2 : ℂ) - z
  let δ := Q γ / 2 - |w.re|
  have hQpos : 0 < Q γ := by linarith
  have hstrip : |w.re| < Q γ / 2 := by
    apply (abs_lt).2
    aesop
  have hδ : 0 < δ := by positivity
  have hdenPos := realDenom_pos hγ (by linarith : 0 < t)
  have hK : 0 < tailConst γ := tailConst_pos hγ
  have hdenom :
      ‖(realDenom γ t : ℂ) * (t : ℂ)‖ = realDenom γ t * t := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hdenPos, abs_of_pos (by linarith : 0 < t)]
  have hcomplexDenom : complexDenom γ (t : ℂ) = (realDenom γ t : ℂ) := by
    simp [complexDenom, realDenom]
  have hcomplexDenomNorm : ‖complexDenom γ (t : ℂ)‖ = realDenom γ t := by
    rw [hcomplexDenom, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos]
  have hlinear :
      ‖-2 * w * Complex.exp (-(t : ℂ)) * complexDenom γ (t : ℂ) /
          ((realDenom γ t : ℂ) * (t : ℂ))‖ ≤
        2 * ‖w‖ * Real.exp (-t) := by
    have hexp : ‖Complex.exp (-(t : ℂ))‖ = Real.exp (-t) := by
      simp [Complex.norm_exp]
    calc
      _ = (2 * ‖w‖ * Real.exp (-t) * realDenom γ t) /
          (realDenom γ t * t) := by
            rw [norm_div, hdenom]
            simp [hcomplexDenomNorm, hexp]
      _ ≤ 2 * ‖w‖ * Real.exp (-t) := by
        have htpos : 0 < t := by linarith
        have hcoef : 0 ≤ 2 * ‖w‖ * Real.exp (-t) := by positivity
        have hDt : realDenom γ t ≤ realDenom γ t * t := by
          simpa using mul_le_mul_of_nonneg_left ht hdenPos.le
        rw [div_le_iff₀ (mul_pos hdenPos htpos)]
        exact mul_le_mul_of_nonneg_left hDt hcoef
  have hnonzero : (realDenom γ t : ℂ) * (t : ℂ) ≠ 0 := by
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hdenPos.ne')
      (Complex.ofReal_ne_zero.mpr (by linarith : t ≠ 0))
  have hnonlinear :
      ‖(Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))) /
          (realDenom γ t : ℂ)‖ ≤
        (tailConst γ)⁻¹ * Real.exp (-δ * t) := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdenPos]
    have hSinh : ‖Complex.sinh (w * (t / 2))‖ ≤ Real.exp (|w.re| * (t / 2)) := by
      calc
        _ ≤ Real.exp |(w * (t / 2)).re| := complex_sinh_norm_le_exp_abs_re _
        _ = Real.exp (|w.re| * (t / 2)) := by
          have hre : (w * (t / 2)).re = w.re * (t / 2) := by simp
          rw [hre, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
    have hCosh : ‖Complex.cosh (w * (t / 2))‖ ≤ Real.exp (|w.re| * (t / 2)) := by
      calc
        _ ≤ Real.exp |(w * (t / 2)).re| := complex_cosh_norm_le_exp_abs_re _
        _ = Real.exp (|w.re| * (t / 2)) := by
          have hre : (w * (t / 2)).re = w.re * (t / 2) := by simp
          rw [hre, abs_mul, abs_of_nonneg (by positivity : 0 ≤ t / 2)]
    have hprod :
        ‖Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2))‖ ≤
          Real.exp (|w.re| * t) := by
      calc
        _ = ‖Complex.sinh (w * (t / 2))‖ * ‖Complex.cosh (w * (t / 2))‖ := norm_mul ..
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
              (Real.exp _ * Real.exp (Q γ / 2 * t)) := by ring
          _ = Real.exp (|w.re| * t) := by
            rw [inv_mul_cancel₀ hK.ne', ← Real.exp_add]
            rw [show -δ * t + Q γ / 2 * t = |w.re| * t by ring]
            simp
      calc
        _ ≥ (tailConst γ)⁻¹ * Real.exp _ *
            (tailConst γ * Real.exp _) :=
              mul_le_mul_of_nonneg_left (realDenom_ge_tail_exp hγ ht) (by positivity)
        _ = _ := hfactor
    have hdiv :
        Real.exp _ / realDenom γ t ≤
          (tailConst γ)⁻¹ * Real.exp _ :=
      (div_le_iff₀ hdenPos).2 hden
    calc
      _ = ‖Complex.sinh _ * Complex.cosh _‖ /
          realDenom γ t := rfl
      _ ≤ Real.exp (|w.re| * t) / realDenom γ t :=
        div_le_div_of_nonneg_right hprod hdenPos.le
      _ ≤ _ := hdiv
  have hsum := norm_add_le
    (-2 * w * Complex.exp (-(t : ℂ)) * complexDenom γ (t : ℂ) /
      ((realDenom γ t : ℂ) * (t : ℂ)))
    (Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) /
      (realDenom γ t : ℂ))
  have hEq : upsilonLogIntegrandDeriv γ z t =
      (-2 * w * Complex.exp (-(t : ℂ)) * complexDenom γ (t : ℂ) /
          ((realDenom γ t : ℂ) * (t : ℂ))) +
        (Complex.sinh (w * (t / 2)) * Complex.cosh (w * (t / 2)) /
          (realDenom γ t : ℂ)) := by
    rw [upsilonLogIntegrandDeriv, zDerivNum, zDerivNumComplex]
    have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
    have hDC : (realDenom γ t : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hdenPos.ne'
    field_simp [htC, hDC]
    have hqw : (Q γ : ℂ) - 2 * z = 2 * w := by
      dsimp [w]
      ring
    rw [hqw]
    have harg : (2 * w) * (t : ℂ) / 2 ^ 2 = (t : ℂ) * w / 2 := by ring
    rw [harg]
    ring
  rw [hEq]
  calc
    _ ≤ 2 * ‖w‖ * Real.exp (-t) +
        (tailConst γ)⁻¹ * Real.exp (-δ * t) := by
          exact hsum.trans (add_le_add hlinear hnonlinear)
    _ = _ := by aesop

end

end

private lemma upsilonLogIntegrandDeriv_aestronglyMeasurable (γ : ℝ) (z : ℂ) :
    AEStronglyMeasurable (fun t : ℝ => upsilonLogIntegrandDeriv γ z t) volume := by
  have hnum : Measurable (fun t => zDerivNum γ ((Q γ / 2) - z) t) := by
    fun_prop [zDerivNum, zDerivNumComplex, complexDenom]
  have hden : Measurable (fun t =>
      (realDenom γ t) * (t : ℂ)) := by
    fun_prop [realDenom]
  exact (hnum.div hden).aestronglyMeasurable
section
variable {γ : ℝ}
section
variable (hγ : 0 < γ)
include hγ

private lemma upsilonLog_hasDerivAt (hγ2 : γ < 2)
    (z₀ : ℂ) (hz₀ : 0 < z₀.re) (hzQ : z₀.re < Q γ) :
    HasDerivAt (fun z : ℂ => upsilonLog γ z)
      (∫ t in Ioi (0 : ℝ), upsilonLogIntegrandDeriv γ z₀ t) z₀ := by
  let margin := min z₀.re (Q γ - z₀.re)
  let r := margin / 2
  let q := (Q γ / 2 : ℂ)
  let w₀ := q - z₀
  let W := ‖w₀‖ + r
  let B := (tailConst γ)⁻¹
  have hmargin : 0 < margin := by
    positivity
  have hr : 0 < r := by positivity
  have hQpos : 0 < Q γ := by linarith
  have hqre : q.re = Q γ / 2 := by aesop
  have hWnonneg : 0 ≤ W := by positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact le_of_lt (inv_pos.mpr (tailConst_pos hγ))
  obtain ⟨C, hC, hTaylor⟩ := exists_zDerivNum_taylor_bound hγ w₀ r
  let A : ℝ := 4 * C * Real.exp 1 + 2 * W
  let bound : ℝ → ℝ := fun t => A * Real.exp (-t) + B * Real.exp (-r * t)
  have hA_nonneg : 0 ≤ A := by positivity
  have hA_lower : 2 * W ≤ A := by
    bound
  have hs : Metric.ball z₀ r ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ hr
  have hz_near (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
      |z.re - z₀.re| < r := by
    have hdist : dist z z₀ < r := Metric.mem_ball.mp hz
    have hre := (Complex.abs_re_le_norm (z - z₀)).trans_lt (by
      simpa [dist_eq_norm] using hdist)
    simpa [Complex.sub_re] using hre
  have hz_real_bounds (z : ℂ) (hz : z ∈ Metric.ball z₀ r) :
      r < z.re ∧ z.re < Q γ - r := by
    have hc' := abs_lt.mp (hz_near z hz)
    have hmleft : margin ≤ z₀.re := min_le_left ..
    have hmright : margin ≤ Q γ - z₀.re := min_le_right ..
    constructor <;> grind
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
      have heq : ((Q γ / 2 : ℂ) - z) - w₀ = z₀ - z := by ring
      rw [heq]
      simp [norm_sub_rev]
    dsimp [W, w₀]
    calc
      ‖(Q γ / 2 : ℂ) - z‖ = ‖w₀ + (z₀ - z)‖ := by
        congr 1
        dsimp [w₀]
        ring
      _ ≤ ‖w₀‖ + ‖z₀ - z‖ := norm_add_le ..
      _ = ‖w₀‖ + dist z z₀ := by rw [dist_eq_norm]; simp [norm_sub_rev]
      _ ≤ ‖w₀‖ + r := by linarith
  have hTaylor_local {z : ℂ} (hz : z ∈ Metric.ball z₀ r)
      {t : ℝ} (ht : t ∈ Icc 0 1) :
      ‖zDerivNum γ ((Q γ / 2 : ℂ) - z) t‖ ≤ C * t ^ 3 := by
    apply hTaylor
    · have hdist : dist ((Q γ / 2 : ℂ) - z) w₀ ≤ r := by
        rw [dist_eq_norm]
        have heq : ((Q γ / 2 : ℂ) - z) - w₀ = z₀ - z := by ring
        rw [heq]
        have hdz : dist z z₀ < r := Metric.mem_ball.mp hz
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
      have hexp : 1 ≤ Real.exp (1 - t) := by
        exact Real.one_le_exp_iff.mpr (by linarith)
      have hexpId : Real.exp (1 - t) = Real.exp 1 * Real.exp (-t) := by
        rw [← Real.exp_add]
        congr 1
      have hcoeff : 4 * C ≤ A * Real.exp (-t) := by
        dsimp [A]
        have h := mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 4 * C)
        rw [hexpId] at h
        linarith only [h, mul_nonneg hWnonneg (Real.exp_pos (-t)).le]
      calc
        _ ≤ 4 * C := (upsilonLogIntegrandDeriv_norm_le_of_taylor hγ z C hC ht ht1 hTaylor')
        _ ≤ A * Real.exp (-t) := hcoeff
        _ ≤ bound t := by
          exact le_add_of_nonneg_right (mul_nonneg hB_nonneg (Real.exp_pos _).le)
    · have ht' : 1 ≤ t := le_of_not_ge ht1
      obtain ⟨hzlow, hzhigh⟩ := hz_real_bounds z hz
      have hzQ' : z.re < Q γ := lt_of_lt_of_le hzhigh (by linarith)
      have hδ : r ≤ Q γ / 2 - |Q γ / 2 - z.re| := by
        have habs := hw_re_margin z hz
        linarith
      have hfirst :
          2 * ‖(Q γ / 2 : ℂ) - z‖ * Real.exp (-t) ≤ A * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right (by
          calc
            2 * ‖(Q γ / 2 : ℂ) - z‖ ≤ 2 * W := by
              exact mul_le_mul_of_nonneg_left (hw_norm_bound z hz) (by norm_num)
            _ ≤ A := hA_lower) (Real.exp_pos _).le
      have hsecond :
          B * Real.exp (-(Q γ / 2 - |Q γ / 2 - z.re|) * t) ≤
            B * Real.exp (-r * t) := by
        apply mul_le_mul_of_nonneg_left _ hB_nonneg
        apply Real.exp_le_exp.mpr
        have ht0 : 0 ≤ t := by linarith
        linarith only [(mul_le_mul_of_nonneg_right hδ ht0)]
      simpa [bound, B] using (upsilonLogIntegrandDeriv_norm_le_tail hγ z (lt_trans hr hzlow) hzQ' ht').trans (add_le_add hfirst hsecond)
  have hF_meas : ∀ᶠ z in 𝓝 z₀,
      AEStronglyMeasurable (fun t => upsilonLogIntegrand γ z t)
        (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [] with z
    exact (upsilonLogIntegrand_aestronglyMeasurable γ z).restrict
  have hF_int : Integrable (fun t => upsilonLogIntegrand γ z₀ t)
      (volume.restrict (Ioi (0 : ℝ))) := by
    exact (upsilonLogIntegrand_integrableOn hγ hγ2 z₀ hz₀ hzQ)
  have hF'_meas : AEStronglyMeasurable
      (fun t => upsilonLogIntegrandDeriv γ z₀ t)
      (volume.restrict (Ioi (0 : ℝ))) :=
    (upsilonLogIntegrandDeriv_aestronglyMeasurable γ z₀).restrict
  have hBound_int : Integrable bound (volume.restrict (Ioi (0 : ℝ))) := by
    have h₁ : IntegrableOn (fun t => A * Real.exp (-t)) (Ioi (0 : ℝ)) := by
      change Integrable (fun t => A * Real.exp (-t))
        (volume.restrict (Ioi (0 : ℝ)))
      simpa [mul_comm] using
        (exp_neg_integrableOn_Ioi 0 (b := 1) (by norm_num)).const_mul A
    have h₂ : IntegrableOn (fun t => B * Real.exp (-r * t)) (Ioi (0 : ℝ)) := by
      change Integrable (fun t => B * Real.exp _)
        (volume.restrict (Ioi (0 : ℝ)))
      simpa [mul_comm] using
        (exp_neg_integrableOn_Ioi 0 hr).const_mul B
    change IntegrableOn (fun t => A * Real.exp (-t) + B * Real.exp _)
      (Ioi (0 : ℝ))
    exact h₁.add h₂
  have hdiff : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ∀ z ∈ Metric.ball z₀ r,
        HasDerivAt (fun z => upsilonLogIntegrand γ z t)
          (upsilonLogIntegrandDeriv γ z t) z := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro z hz
    have hfun : DifferentiableAt ℂ (fun z => upsilonLogIntegrand γ z t) z := by
      fun_prop [upsilonLogIntegrand]
    simpa [deriv_upsilonLogIntegrand hγ ht z] using hfun.hasDerivAt
  obtain ⟨_, hhas⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs hF_meas hF_int hF'_meas hparam_bound hBound_int hdiff
  simpa [upsilonLog] using hhas

/-- The logarithm given by the convergent integral is holomorphic on its defining strip. -/
theorem upsilonLog_differentiableOn (_hγ2 : γ < 2) :
    DifferentiableOn ℂ (fun z => upsilonLog γ z)
      {z | 0 < z.re ∧ z.re < Q γ} := by
  intro z hz
  exact (upsilonLog_hasDerivAt hγ _hγ2 z hz.1 hz.2).differentiableAt.differentiableWithinAt

end

end

end

end DOZZ.Proofs

end
