module
/-
Native q=1 contour convergence from proved actual-zeta growth and genuine
compact-test Mellin decay. McColm's selected strip-tail proof pattern is
adapted at revision 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1 (MIT-0).
Mathlib and existing rectangle Apache attributions retained.
-/
public import MathCollab.Density.Stronger.Atkinson.OrdinaryDivisorResidue
public import MathCollab.Density.Stronger.Atkinson.VoronoiZetaGrowth
public import Mathlib.MeasureTheory.Integral.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import WeylPort.Analytic.RealLaplace

public section

open Complex Set MeasureTheory Filter Topology Asymptotics
open MathCollab.Density.Contour
namespace MathCollab.Density.Stronger.Atkinson

section
variable {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
include g hg
theorem DFIVoronoiTestFunction.exists_ordinaryDivisorMellin_strip_decay :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, -(1/2 : ℝ) ≤ σ → σ ≤ 3/2 → ∀ u : ℝ,
      1 ≤ |u| → ‖ordinaryDivisorMellinIntegrand g ((σ : ℂ)+(u : ℂ)*I)‖ ≤
        C / (1+|u|)^2 := by
  obtain ⟨D,hD,hmel⟩ := hg.exists_mellin_weighted_strip_bound 6
  refine ⟨240^2 * D, by positivity, ?_⟩
  intro σ hσ hσ' u hu
  have hz := norm_riemannZeta_voronoi_strip hσ hσ' hu
  have hm := hmel σ hσ hσ' u
  pm_569 u
  rw [ordinaryDivisorMellinIntegrand, norm_mul, norm_pow]
  calc
    _ ≤ (240*(1+|u|)^2)^2 * ‖mellin g ((σ : ℂ)+(u : ℂ)*I)‖ * (1+|u|)^2 := by gcongr
    _ = 240^2 * ((1+|u|)^6 * ‖mellin g ((σ : ℂ)+(u : ℂ)*I)‖) := by ring
    _ ≤ 240^2 * D := by gcongr

theorem DFIVoronoiTestFunction.continuous_ordinaryDivisorMellin_vertical {σ : ℝ} (hσ : σ ≠ 1) :
    Continuous (fun u : ℝ => ordinaryDivisorMellinIntegrand g ((σ : ℂ)+(u : ℂ)*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have hz : (σ : ℂ)+(u : ℂ)*I ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    simpa using hσ (by simpa using hr)
  have hv : ContinuousAt (fun v : ℝ => (σ : ℂ)+(v : ℂ)*I) u := by fun_prop
  simpa only [Function.comp_def, Pi.mul_apply, Pi.pow_apply, ordinaryDivisorMellinIntegrand] using
    ContinuousAt.comp (f := fun v : ℝ => (σ : ℂ)+(v : ℂ)*I)
      (g := riemannZeta ^ 2 * mellin g)
      (((differentiableAt_riemannZeta hz).pow 2).mul
        (hg.differentiable_mellin _)).continuousAt hv
end

/-- Explicit analytic helper: a continuous function with a quadratic tail is integrable. -/
theorem integrable_of_continuous_quadratic_tail {f : ℝ → ℂ} (hf : Continuous f)
    {C : ℝ} (hC : 0 ≤ C) (htail : ∀ u : ℝ, 1 ≤ |u| → ‖f u‖ ≤ C/(1+|u|)^2) :
    Integrable f := by
  have hb (u : ℝ) (hu : 1 ≤ |u|) : ‖f u‖ ≤ C * ‖(1+u^2)⁻¹‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), ← div_eq_mul_inv]
    exact (htail u hu).trans (div_le_div_of_nonneg_left hC (by positivity)
      (by nlinarith [sq_abs u, abs_nonneg u]))
  apply hf.locallyIntegrable.integrable_of_isBigO_atBot_atTop
    (g := fun u : ℝ => (1+u^2)⁻¹) (g' := fun u : ℝ => (1+u^2)⁻¹)
  · apply IsBigO.of_bound C
    filter_upwards [eventually_le_atBot (-1 : ℝ)] with u hu
    exact hb u (by rw [abs_of_nonpos (by linarith)]; linarith)
  · exact integrable_inv_one_add_sq.integrableAtFilter atBot
  · apply IsBigO.of_bound C
    pm_359 u hu
    exact hb u (by rw [abs_of_nonneg (by linarith)]; exact hu)
  · exact integrable_inv_one_add_sq.integrableAtFilter atTop

section
variable {g : ℝ → ℂ} (hg : DFIVoronoiTestFunction g)
include g hg
theorem DFIVoronoiTestFunction.integrable_ordinaryDivisorMellin_vertical {σ : ℝ}
    (hσ : -(1/2 : ℝ) ≤ σ) (hσ' : σ ≤ 3/2) (hne : σ ≠ 1) :
    Integrable (fun u : ℝ => ordinaryDivisorMellinIntegrand g ((σ : ℂ)+(u : ℂ)*I)) := by
  obtain ⟨C,hC,hdecay⟩ := hg.exists_ordinaryDivisorMellin_strip_decay
  exact integrable_of_continuous_quadratic_tail
    (hg.continuous_ordinaryDivisorMellin_vertical hne) hC (hdecay σ hσ hσ')

theorem DFIVoronoiTestFunction.ordinaryDivisor_horizontal_limits :
    Tendsto (fun H : ℝ => HIntegral' (ordinaryDivisorMellinIntegrand g) (-1/2) (3/2) H)
        atTop (𝓝 0) ∧
      Tendsto (fun H : ℝ => HIntegral' (ordinaryDivisorMellinIntegrand g) (-1/2) (3/2) (-H))
        atTop (𝓝 0) := by
  obtain ⟨C,hC,hdecay⟩ := hg.exists_ordinaryDivisorMellin_strip_decay
  have hbound (H : ℝ) (hH : 1 ≤ |H|) :
      ‖HIntegral (ordinaryDivisorMellinIntegrand g) (-1/2) (3/2) H‖ ≤
        C / (1+|H|)^2 * 2 := by
    have hInt := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -(1/2 : ℝ)) (b := (3/2 : ℝ))
      (f := fun x : ℝ => ordinaryDivisorMellinIntegrand g ((x : ℂ)+(H : ℂ)*I))
      (C := C/(1+|H|)^2) (fun x hx => by
        have hx' := Set.uIoc_subset_uIcc hx
        rw [Set.uIcc_of_le (by norm_num : -(1/2 : ℝ) ≤ 3/2)] at hx'
        exact hdecay x hx'.1 hx'.2 H hH)
    convert hInt using 1 <;> norm_num [HIntegral]
  have hEnv : Tendsto (fun H : ℝ => C/(1+|H|)^2*2) atTop (𝓝 0) := by
    pm_193
    simpa using h.mul_const 2
  have htop : Tendsto (fun H : ℝ => HIntegral (ordinaryDivisorMellinIntegrand g) (-1/2) (3/2) H)
      atTop (𝓝 0) := by
    pm_6749
    pm_359 H hH
    exact hbound H (by rw [abs_of_nonneg (by linarith)]; exact hH)
  have hbottom : Tendsto (fun H : ℝ => HIntegral (ordinaryDivisorMellinIntegrand g) (-1/2) (3/2) (-H))
      atTop (𝓝 0) := by
    pm_6749
    pm_359 H hH
    simpa only [abs_neg] using hbound (-H) (by rw [abs_neg, abs_of_nonneg (by linarith)]; exact hH)
  constructor
  pm_376 htop.const_smul
  pm_376 hbottom.const_smul
end

end MathCollab.Density.Stronger.Atkinson
