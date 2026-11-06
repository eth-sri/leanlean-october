module
public import WrittenDensity.Common

@[expose] public section

set_option autoImplicit false
noncomputable section
namespace Montgomery.WrittenDensity
open MathCollab.Density
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_v7_A_1 {σ ε : ℝ} (_hlo : (7/10) ≤ σ)
    (_hhi : σ ≤ (12/17)) (_hε : 0 < ε) :
    DensityBound σ ((6 + (-6 * σ)) / (-3 + (8 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : (7/10) ≤ σ := by linarith
  have hh : σ ≤ (12/17) := by linarith
  apply density_weaken (Montgomery.Refined.refined_density_middle (by linarith) (by linarith) _hε)
  have hd1 : 0 < (3 + (7 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-3 + (8 * σ)) := by linarith
  have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 6/(-3 + (8 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (72 + (-102 * σ)) := by
      calc
        0 ≤ 102*((12/17)-σ) := by positivity
        _ = (72 + (-102 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_oct2_mixed_4 {σ ε : ℝ} (_hlo : (19/22) ≤ σ)
    (_hhi : σ ≤ (23/26)) (_hε : 0 < ε) :
    DensityBound σ ((24 + (-24 * σ)) / (-11 + (30 * σ))) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  by_cases hc0 : σ ≤ (2905/3354)
  ·
    have hl : (19/22) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-11 + (30 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 24/(-11 + (30 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1418364 + (2455704 * σ)) := by
        calc
          0 ≤ (6479243784/23)*((2905/3354)-σ)+(6535724976/23)*(σ-(19/22)) := by positivity
          _ = (-1418364 + (2455704 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (2905/3354) ≤ σ := by linarith
  have hh : σ ≤ (7/8) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row8 (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1015 + (2742 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-11 + (30 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 24/(-11 + (30 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-468 + (648 * σ)) := by
      calc
        0 ≤ (1251072/119)*((7/8)-σ)+(1328184/119)*(σ-(2905/3354)) := by positivity
        _ = (-468 + (648 * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring
/-- Exact full written-source conclusion, proved here by checked native density and strict actual zero-freeness. This does not certify the original analytic route. -/
theorem source_oct2_mixed_5 {σ ε : ℝ} (_hlo : (23/26) ≤ σ)
    (_hhi : σ < 1) (_hε : 0 < ε) :
    DensityBound σ ((6 + (-6 * σ)) / (3 + σ)) ε := by
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  linarith
end Montgomery.WrittenDensity
