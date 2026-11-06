module
public import MathCollab.Density.DetectorMellin
public import MathCollab.Density.DetectorGamma
public import MathCollab.Density.AbelZetaGrowth
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import WeylPort.Analytic.RealLaplace

public section

open Complex MeasureTheory Set Filter
open scoped Topology
namespace MathCollab.Density

/-- A coarse bound uniform in the imaginary part, adequate for contour limits. -/
theorem norm_zetaMollifier_le_cutoff (X : ℝ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖zetaMollifier X s‖ ≤ (⌊X⌋₊ : ℝ) := by
  unfold zetaMollifier
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 ⌊X⌋₊,
        ‖(ArithmeticFunction.moebius d : ℂ)*(d : ℂ)^(-s)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.Icc 1 ⌊X⌋₊, (1 : ℝ) := Finset.sum_le_sum fun d hd => by
      have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
      pm_77 hdreal d hdpos
      pm_501
      have hp : (d : ℝ)^(-s.re) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hdreal (by linarith)
      exact (mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (by positivity) _)).trans (by grind)
    _ = _ := by simp

/-- Actual zeta has a global linear majorant on the critical line. This is
coarse growth for contour convergence, not a Weyl estimate. -/
theorem norm_riemannZeta_critical_le_linear (t : ℝ) :
    ‖riemannZeta ((1/2 : ℂ)+(t : ℂ)*I)‖ ≤ 4*(1+|t|) := by
  let s : ℂ := (1/2 : ℂ)+(t : ℂ)*I
  have hre : s.re = 1/2 := by aesop
  have hs : s ≠ 1 := by intro h; have he := congrArg Complex.re h; simp_all
  have hden : (1/2 : ℝ) ≤ ‖s-1‖ := by
    have h := Complex.abs_re_le_norm (s-1)
    norm_num [hre] at h ⊢
    exact h
  have hr := ZetaGrowth.norm_abelZetaRemainder_le (s := s) (by simp_all)
  rw [hre] at hr
  norm_num at hr
  have hsn : ‖s‖ ≤ 1+|t| := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    norm_num [s] at h
    linarith
  change ‖riemannZeta s‖ ≤ _
  rw [ZetaGrowth.riemannZeta_eq_abel (by simp_all) hs]
  calc
    _ ≤ ‖s/(s-1)‖ + ‖s*ZetaGrowth.abelZetaRemainder s‖ := norm_sub_le _ _
    _ = ‖s‖/‖s-1‖ + ‖s‖*‖ZetaGrowth.abelZetaRemainder s‖ := by simp_all
    _ ≤ ‖s‖/(1/2)+‖s‖*2 := add_le_add
      (div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) hden)
      (mul_le_mul_of_nonneg_left hr (norm_nonneg _))
    _ ≤ _ := by linarith

/-- The right contour is absolutely integrable for independent X and Y. -/
theorem integrable_detectorKernel_right {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hρ : 3/4 ≤ ρ.re) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((1/2 : ℝ) : ℂ)+(t : ℂ)*I)) := by
  pm_4317 verticalIntegrable_mellin_smoothedDetector
  have hp : Continuous (fun t : ℝ => (Y : ℂ)^(line t)) := by
    apply Continuous.cpow continuous_const (by fun_prop)
    intro t
    left; simp_all
  have hb : ∀ t : ℝ, ‖(Y : ℂ)^(line t)‖ ≤ Y^(1/2 : ℝ) := by
    intro t
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
    aesop
  pm_4316

set_option hygiene false in
macro "pf_35" x1:term:max x2:ident : tactic => `(tactic| (
  let a : ℝ := 1/2-ρ.re
  let line := fun t : ℝ => (a : ℂ)+(t : ℂ)*I
  have he : ∀ t : ℝ, ρ+line t = (1/2 : ℂ)+((ρ.im+t : ℝ) : ℂ)*I := by
    intro t
    apply Complex.ext <;> simp [line, a]
  have hg := ($x1:term ρ.re hβ hβ').2.1
  have hc : Continuous (fun t : ℝ => detectorKernel ρ X Y (line t)) := by
    unfold detectorKernel
    apply Continuous.mul
    · apply Continuous.mul
      · apply Continuous.mul
        · apply Continuous.cpow continuous_const (by dsimp [line]; fun_prop)
          intro t
          left; simpa using hY
        · exact $x2:ident (by dsimp [a]; linarith) (by dsimp [a]; linarith)
      · apply continuous_iff_continuousAt.mpr
        intro t
        exact ContinuousAt.comp' (differentiableAt_zetaMollifier X (ρ+line t)).continuousAt
          (by dsimp [line]; fun_prop)
    · apply continuous_iff_continuousAt.mpr
      intro t
      apply ContinuousAt.comp' (differentiableAt_riemannZeta ?_).continuousAt
        (by dsimp [line]; fun_prop)
      rw [he]
      intro h
      have hr := congrArg Complex.re h
      norm_num at hr
  let C : ℝ := Y^a*(⌊X⌋₊ : ℝ)*4*(1+|ρ.im|)
  have hbound : ∀ t : ℝ, ‖detectorKernel ρ X Y (line t)‖ ≤
      C*((1+|t|)*‖Complex.Gamma (line t)‖) := by
    intro t
    have hm := norm_zetaMollifier_le_cutoff X (s := ρ+line t) (by rw [he]; norm_num)
    have hz := norm_riemannZeta_critical_le_linear (ρ.im+t)
    rw [← he] at hz
    have hab := abs_add_le ρ.im t
    have hzt : ‖riemannZeta (ρ+line t)‖ ≤ 4*(1+|ρ.im|)*(1+|t|) := by
      nlinarith [mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t)]
    dsimp [detectorKernel]
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hY]
    have hre : (line t).re = a := by simp [line]
    rw [hre]
    calc
      _ ≤ (Y^a*‖Complex.Gamma (line t)‖)*(⌊X⌋₊ : ℝ)*(4*(1+|ρ.im|)*(1+|t|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hm (by positivity)) hzt (norm_nonneg _) (by positivity)
      _ = _ := by dsimp [C]; ring
  exact (hg.const_mul C).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound)))
/-- The shifted contour is absolutely integrable using only linear zeta growth. -/
theorem integrable_detectorKernel_left {ρ : ℂ} {X Y : ℝ}
    (hY : 0 < Y) (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re ≤ 1) :
    Integrable (fun t : ℝ => detectorKernel ρ X Y (((1/2-ρ.re : ℝ) : ℂ)+(t : ℂ)*I)) := by pf_35 uniform_detector_gamma_mass.choose_spec.2 continuous_Gamma_detector_strip

/-- One ordinate-independent horizontal majorant for arbitrary fixed X,Y,rho. -/
theorem norm_detectorKernel_horizontal {ρ : ℂ} {X Y u t : ℝ}
    (hY : 1 ≤ Y) (hβ' : ρ.re ≤ 1)
    (hu : 1/2-ρ.re ≤ u) (hu' : u ≤ 1/2) (ht : |ρ.im|+1 ≤ |t|) :
    ‖detectorKernel ρ X Y ((u : ℂ)+(t : ℂ)*I)‖ ≤
      (60*Y^(1/2 : ℝ)*(⌊X⌋₊ : ℝ)*(2+|ρ.im|)) * (1+|t|)^3*Real.exp (-|t|) := by
  pm_5103 s u t I
  have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one hY
  pm_1468 hure huim
  have him : 1 ≤ |(ρ+s).im| := by
    pm_7438 huim
    have he : ρ.im+t+-ρ.im = t := by ring
    rw [he, abs_neg] at h
    linarith
  have hz := ZetaGrowth.norm_riemannZeta_le_five_mul_norm
    (s := ρ+s) (by rw [hure]; linarith) him
  have hnorm : ‖ρ+s‖ ≤ 2+|ρ.im|+|t| := by
    have h := Complex.norm_le_abs_re_add_abs_im (ρ+s)
    rw [hure, huim, abs_of_nonneg (show 0 ≤ ρ.re+u by linarith)] at h
    have hh := abs_add_le ρ.im t
    linarith
  have hz' : ‖riemannZeta (ρ+s)‖ ≤ 5*(2+|ρ.im|)*(1+|t|) := by
    nlinarith [mul_nonneg (abs_nonneg ρ.im) (abs_nonneg t), abs_nonneg t]
  have hm := norm_zetaMollifier_le_cutoff X (s := ρ+s) (by rw [hure]; linarith)
  have hg := norm_Gamma_contour_strip (a := u) (t := t)
    (by linarith) (by linarith) (by linarith [abs_nonneg ρ.im])
  have hp : ‖(Y : ℂ)^s‖ ≤ Y^(1/2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hYpos]
    exact Real.rpow_le_rpow_of_exponent_le hY (by simpa [s] using hu')
  change ‖(Y : ℂ)^s * Complex.Gamma s * zetaMollifier X (ρ+s) * riemannZeta (ρ+s)‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul]
  calc
    _ ≤ Y^(1/2 : ℝ)*(12*(1+|t|)^2*Real.exp (-|t|))*(⌊X⌋₊ : ℝ)*
        (5*(2+|ρ.im|)*(1+|t|)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right
        (mul_le_mul hp hg (norm_nonneg _) (by positivity)) (norm_nonneg _)) hz'
        (norm_nonneg _) (by positivity) |>.trans (by gcongr)
    _ = _ := by ring

theorem tendsto_detector_horizontal_majorant (C : ℝ) :
    Tendsto (fun R : ℝ => C*(1+R)^3*Real.exp (-R)) atTop (𝓝 0) := by
  pm_7370 Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero
  have h := (((h0.add (h1.const_mul 3)).add (h2.const_mul 3)).add h3).const_mul C
  convert h using 1
  · funext R
    ring
  · simp

/-- Both horizontal integrals vanish as the independent rectangle height grows. -/
theorem tendsto_detector_horizontal_integral {ρ : ℂ} {X Y ε : ℝ}
    (hY : 1 ≤ Y) (hβ : 3/4 ≤ ρ.re) (hβ' : ρ.re ≤ 1) (hε : |ε| = 1) :
    Tendsto (fun R : ℝ => ∫ u in (1/2-ρ.re)..(1/2 : ℝ),
      detectorKernel ρ X Y ((u : ℂ)+((ε*R : ℝ) : ℂ)*I)) atTop (𝓝 0) := by pm_4318

end MathCollab.Density
