module
public import WrittenDensity.Common
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.WrittenDensity
open MathCollab.Density
section
variable {σ ε : ℝ}
include σ ε
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_A_1 (_hlo : (7/10) ≤ σ)
    (_hhi : σ ≤ (12/17)) (_hε : 0 < ε) :
    DensityBound σ ((6 + (-6 * σ)) / (-3 + (8 * σ))) ε := by
  pm_538
  grind
  pm_428
  have hl : (7/10) ≤ σ := by linarith
  have hh : σ ≤ (12/17) := by linarith
  pm_607
  have hd2 : (0:ℝ) < (-3 + (8 * σ)) := by linarith
  have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 6/(-3 + (8 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (72 + (-102 * σ)) := by
      grind
    grind
  pm_6654
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_oct2_mixed_4 (_hlo : (19/22) ≤ σ)
    (_hhi : σ ≤ (23/26)) (_hε : 0 < ε) :
    DensityBound σ ((24 + (-24 * σ)) / (-11 + (30 * σ))) ε := by
  pm_538
  · exact density_of_actual_zero hz
  pm_428
  pm_7085 hc0
  ·
    have hl : (19/22) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-11 + (30 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 24/(-11 + (30 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1418364 + (2455704 * σ)) := by
        grind
      grind
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    grind
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-11 + (30 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 24/(-11 + (30 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-468 + (648 * σ)) := by
      grind
    nlinarith only [hc]
  pm_6654
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_oct2_mixed_5 (_hlo : (23/26) ≤ σ)
    (_hhi : σ < 1) (_hε : 0 < ε) :
    DensityBound σ ((6 + (-6 * σ)) / (3 + σ)) ε := by
  pm_538
  · exact density_of_actual_zero hz
  pm_428
  linarith
end
end Montgomery.WrittenDensity
