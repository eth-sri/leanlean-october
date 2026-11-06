module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction; see third_party/twelfth/ATKINSON_CORRECTION_SERIES_MANIFEST.json.
Mathlib and the nonstationary foundations retain their Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCorrectionBounds
public import MathCollab.Density.Stronger.Atkinson.AtkinsonCarrierIntegrals
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Complex MeasureTheory Set
open MathCollab.Density.Stronger.Fourth
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonCorrectionSum (T G L : ℝ) : ℂ := ∑' n : ℕ, atkinsonCorrectionTerm T G L n

theorem atkinsonTwoTermCarrierIntegral_eq_leading_sub_correction (T G L : ℝ) (n : ℕ) :
    atkinsonTwoTermCarrierIntegral T G L n =
      atkinsonLeadingIntegral T G L n - atkinsonCorrectionIntegral T G L n := by
  unfold atkinsonTwoTermCarrierIntegral atkinsonLeadingIntegral atkinsonCorrectionIntegral
  ring

theorem zetaAtkinsonTwoTerm_eq_leading_sub_correction {T G L : ℝ}
    (hT : 0 < T) (hG : 0 < G) (hL : 0 < L) (hwidth : 8 * L ≤ G) (n : ℕ) :
    zetaAtkinsonTwoTerm T G L n = atkinsonLeadingTerm T G L n - atkinsonCorrectionTerm T G L n := by
  rw [zetaAtkinsonTwoTerm_eq_carrierIntegral hT hG hL hwidth,
    atkinsonTwoTermCarrierIntegral_eq_leading_sub_correction]
  unfold atkinsonLeadingTerm atkinsonCorrectionTerm
  ring

theorem summable_atkinsonCorrectionTerm {T G L : ℝ}
    (hT : 1 ≤ T) (hG : 0 < G) (hGT : G ^ 2 ≤ 2 * T) (hL : 0 < L) (hwidth : 8 * L ≤ G) :
    Summable (atkinsonCorrectionTerm T G L) := by pm_4378 exists_norm_atkinsonCorrectionTerm_le

theorem exists_norm_atkinsonCorrectionSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      0 < L → 8 * L ≤ G → ‖atkinsonCorrectionSum T G L‖ ≤ C * G := by pm_4379 exists_norm_atkinsonCorrectionTerm_le summable_atkinsonCorrectionTerm atkinsonCorrectionTerm

end MathCollab.Density.Stronger.Atkinson
