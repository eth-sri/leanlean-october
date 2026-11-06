module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.SmoothDivisorTail

@[expose] public section

open Complex Filter MeasureTheory Set Topology MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth MathCollab.Density.Contour
open scoped Interval ComplexConjugate ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem exists_zetaSquareLocalMean_le_smooth_divisor {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T G : ℝ,
      T₀ ≤ T → 0 < G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaSmoothDivisorSum T G (Real.log T)).re + C * G * Real.log T := by
  obtain ⟨C, hC, B, hB, hsource⟩ := exists_zetaSquareLocalMean_le_short_divisor hδ
  obtain ⟨B₁, hB₁, htail⟩ := exists_zetaSmoothDivisor_log_tail_bound 0
  have hev : ∀ᶠ T : ℝ in atTop, ∀ G : ℝ, 0 < G → G ≤ T ^ (1 / 2 - δ) →
      (∫ t in T - G..T + G, zetaMomentCriticalNorm t ^ 2) ≤
        2 * Real.exp 1 * (zetaSmoothDivisorSum T G (Real.log T)).re +
          (C + 2 * Real.exp 1) * G * Real.log T := by
    filter_upwards [eventually_zeta_source_log_window_scales hδ, eventually_ge_atTop B,
      eventually_ge_atTop B₁] with T hscale hTB hTB₁
    intro G hG hwidth
    have hmain := hsource T G hTB hG hwidth
    have ht := htail T G hTB₁ hG (hscale.2.2 G hG hwidth).1
    simp only [neg_zero, Real.rpow_zero, mul_one] at ht
    have hre := (Complex.abs_re_le_norm
      (zetaSmoothDivisorSum T G (Real.log T) - zetaShortQuadraticDivisorSum T G (Real.log T))).trans ht
    simp only [Complex.sub_re] at hre
    have hreal : (zetaShortQuadraticDivisorSum T G (Real.log T)).re ≤
        (zetaSmoothDivisorSum T G (Real.log T)).re + G := by
      linarith [(abs_le.mp hre).1]
    have hscaled := mul_le_mul_of_nonneg_left hreal (by positivity : 0 ≤ 2 * Real.exp 1)
    have hGlog : G ≤ G * Real.log T := by nlinarith [hscale.2.1]
    have hextra := mul_le_mul_of_nonneg_left hGlog (by positivity : 0 ≤ 2 * Real.exp 1)
    nlinarith
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨C + 2 * Real.exp 1, by positivity, max 8 T₁, le_max_left _ _, ?_⟩
  intro T G hT hG hwidth
  exact hT₁ T ((le_max_right _ _).trans hT) G hG hwidth

