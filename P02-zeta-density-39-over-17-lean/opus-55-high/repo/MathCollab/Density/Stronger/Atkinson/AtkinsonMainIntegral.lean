module
/-
Copyright (c) 2026 S. McColm. Selected proof slice at revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
See third_party/twelfth/ATKINSON_MAIN_PLUS_MANIFEST.json and third_party/twelfth/LICENSE-MIT-0. Mathlib dependencies retain Apache-2.0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonMainWeight
public import MathCollab.Density.Stronger.Atkinson.MainReflection
public import MathCollab.Density.Stronger.Atkinson.AtkinsonVoronoiTerms
public import MathCollab.Density.Stronger.Atkinson.SourceLogScales
import WeylPort.Analytic.RealLaplace

@[expose] public section

open Complex Filter MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
open scoped ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem zetaAtkinsonVoronoiMain_eq_reflection {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    zetaAtkinsonVoronoiMain T G L =
      ∫ x in (T / 16)..T, zetaAtkinsonMainWeight T G L x * ((x : ℂ)⁻¹ *
        Complex.exp (((T * Real.log x - 2 * Real.pi * x : ℝ) : ℂ) * I)) := by
  have he : zetaAtkinsonVoronoiMain T G L =
      ∫ x : ℝ in Icc (T / 16) T,
        ((Real.log x : ℂ) + 2 * Real.eulerMascheroniConstant) * zetaAtkinsonDivisorTest T G L x := by
    pm_4382
    have hz : zetaAtkinsonDivisorTest T G L x = 0 := by
      pm_411
      pm_7094 hs
    rw [hz, mul_zero]
  rw [he, intervalIntegral.integral_of_le (by linarith : T / 16 ≤ T),
    ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  exact (zetaAtkinsonMainWeight_carrier hT
    (lt_of_lt_of_le (by positivity : 0 < T / 16) hx.1) G L).symm

theorem exists_norm_zetaAtkinsonVoronoiMain_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 16 ≤ T → 1 ≤ Real.log T →
      0 < G → G ^ 2 ≤ 2 * T → 0 < L → 8 * L ≤ G →
      ‖zetaAtkinsonVoronoiMain T G L‖ ≤ C * G * Real.log T := by
  obtain ⟨C, hC, hweight⟩ := exists_intervalC1Bound_zetaAtkinsonMainWeight
  refine ⟨48 * C, by positivity, ?_⟩
  intro T G L hT hlog hG hGT hL hwidth
  have hT0 : 0 < T := by linarith
  rw [zetaAtkinsonVoronoiMain_eq_reflection hT0 hG hL hwidth]
  have h := (hweight T G L hT hlog hG hGT hL).reflection_source hT0
  convert h using 1
  have hs : Real.sqrt T ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hT0)
  field_simp

theorem exists_zetaAtkinsonVoronoiMain_log_bound {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 16 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonVoronoiMain T G (Real.log T)‖ ≤ C * G * Real.log T := by
  obtain ⟨C, hC, hbound⟩ := exists_norm_zetaAtkinsonVoronoiMain_le
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, T ^ δ ≤ G → G ≤ T ^ (1 / 2 - δ) →
      ‖zetaAtkinsonVoronoiMain T G (Real.log T)‖ ≤ C * G * Real.log T := by
    pm_4344
    exact hbound T G (Real.log T) hsupport.1 hscale.2.1 hG
      (hscale.2.2 G hG hupper).1 hlog hwidth
  pm_4343
  exact hB T ((le_max_right _ _).trans hT) G hlower hupper

end MathCollab.Density.Stronger.Atkinson
