module
/- Actual short-detector critical-line input, using the audited zeta and
mollifier bounds. This file does not assume a fourth moment. -/
public import MathCollab.Density.DetectorError
public import MathCollab.Density.BandEnergy

@[expose] public section
set_option autoImplicit false
noncomputable section
open Complex MeasureTheory Set Filter MathCollab.Density
open scoped Topology
namespace GuthMaynard.Improvement

def mollifiedNorm (X t : ℝ) : ℝ :=
  ‖riemannZeta ((1/2:ℂ)+(t:ℂ)*I)*zetaMollifier X ((1/2:ℂ)+(t:ℂ)*I)‖

theorem mollifiedNorm_continuous (X : ℝ) : Continuous (mollifiedNorm X) := by
  apply Continuous.norm
  apply Continuous.mul
  · apply continuous_iff_continuousAt.mpr
    intro t
    apply ContinuousAt.comp' (differentiableAt_riemannZeta ?_).continuousAt (by fun_prop)
    intro hh
    have hr := congrArg Complex.re hh
    norm_num at hr
  · apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp' (differentiableAt_zetaMollifier _ _).continuousAt (by fun_prop)

theorem mollifiedNorm_bound (X t : ℝ) :
    mollifiedNorm X t ≤ 4*(⌊X⌋₊:ℝ)*(1+|t|) := by
  have hz := norm_riemannZeta_critical_le_linear t
  have hm := norm_zetaMollifier_le_cutoff X
    (s := (1/2:ℂ)+(t:ℂ)*I) (by norm_num)
  unfold mollifiedNorm
  rw [norm_mul]
  convert mul_le_mul hz hm (norm_nonneg _) (by positivity) using 1; ring

/-- Exact norm identity: the real power of Y retains the actual beta. -/
theorem short_detector_kernel_norm {ρ : ℂ} {Y : ℝ} (hY : 0 < Y) (X t : ℝ) :
    ‖detectorKernel ρ X Y (((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I)‖ =
      Y^(1/2-ρ.re)*‖Complex.Gamma (((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I)‖*
        mollifiedNorm X (ρ.im+t) := by
  have he : ρ+(((1/2-ρ.re:ℝ):ℂ)+(t:ℂ)*I) = (1/2:ℂ)+((ρ.im+t:ℝ):ℂ)*I := by
    apply Complex.ext <;> simp
  unfold detectorKernel mollifiedNorm
  rw [he,norm_mul,norm_mul,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hY]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,Complex.I_re,
    Complex.I_im,mul_zero,zero_mul,sub_self,add_zero]
  ring

/-- Weighted fourth Hölder proved from two audited Cauchy--Schwarz estimates.
Every moment used is explicitly integrable, preventing default-integral artifacts. -/
theorem short_weighted_fourth_holder {g F : ℝ → ℝ} (hg0 : ∀ t, 0 ≤ g t)
    (hg : Integrable g) (hgf : Integrable (fun t => g t*F t))
    (hgf2 : Integrable (fun t => g t*(F t)^2))
    (hgf4 : Integrable (fun t => g t*(F t)^4)) :
    (∫ t, g t*F t)^4 ≤ (∫ t,g t)^3*(∫ t,g t*(F t)^4) := by
  have hfirst := weighted_integral_sq_le hg0 hg hgf hgf2
  have hsecond := weighted_integral_sq_le (f := fun t => (F t)^2) hg0 hg hgf2
    (by simpa only [← pow_mul] using hgf4)
  have h0 : 0 ≤ ∫ t,g t := integral_nonneg hg0
  have h2 : 0 ≤ ∫ t,g t*(F t)^2 := integral_nonneg (fun t => mul_nonneg (hg0 t) (sq_nonneg _))
  have hh := pow_le_pow_left₀ (sq_nonneg _) hfirst 2
  have hs := mul_le_mul_of_nonneg_left hsecond (sq_nonneg (∫ t,g t))
  simp only [← pow_mul] at hh hs
  nlinarith

end GuthMaynard.Improvement
