module
public import WrittenDensity.Common
import WeylPort.Analytic.RealLaplace

public section

set_option maxHeartbeats 0
namespace Montgomery.LiteratureDensity
open MathCollab.Density Montgomery.WrittenDensity
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_1 {σ ε : ℝ} (_hlo : (1/2) ≤ σ)
    (_hhi : σ ≤ (7/10)) (_hε : 0 < ε) :
    DensityBound σ ((-3 + (3 * σ)) / (-2 + σ)) ε := by
  pm_538
  grind
  pm_428
  by_cases hc0 : σ ≤ (9/13)
  ·
    have hl : (1/2) ≤ σ := by linarith
    have hh : σ ≤ (9/13) := by linarith
    apply density_weaken (GuthMaynard.Improvement.ingham_lower_density σ (by linarith) (by linarith) ε _hε)
    have hd1 : 0 < (2 + (-1 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
    have hA : (3:ℝ)/(2 + (-1 * σ)) ≤ 3/(2 + (-1 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ 0 := by
        calc
          0 ≤ 0 := by positivity
          _ = 0 := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
    calc
      _ = (3:ℝ)/(2 + (-1 * σ))*(1-σ) := by ring
      _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
      _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
        pm_6944
  have hl : (9/13) ≤ σ := by linarith
  have hh : σ ≤ (7/10) := by linarith
  pm_607
  have hd2 : (0:ℝ) < (2 + (-1 * σ)) := by linarith
  have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 3/(2 + (-1 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-27 + (39 * σ)) := by
      calc
        0 ≤ 39*(σ-(9/13)) := by positivity
        _ = (-27 + (39 * σ)) := by ring
    nlinarith only [hc]
  pm_2859
  have hpd : ((-2 + σ):ℝ) ≠ 0 := by linarith
  calc
    _ = (18:ℝ)/(3 + (7 * σ))*(1-σ) := by ring
    _ ≤ 3/(2 + (-1 * σ))*(1-σ) := hp
    _ = ((-3 + (3 * σ)) / (-2 + σ)) := by
      pm_6944
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_2 {σ ε : ℝ} (_hlo : (7/10) ≤ σ)
    (_hhi : σ < (19/25)) (_hε : 0 < ε) :
    DensityBound σ ((15 + (-15 * σ)) / (3 + (5 * σ))) ε := by
  pm_2860
  pm_8334
  ·
    have hl : (7/10) ≤ σ := by linarith
    have hh : σ ≤ (12/17) := by linarith
    apply density_weaken (Montgomery.Refined.refined_density_middle (by linarith) (by linarith) _hε)
    have hd1 : 0 < (3 + (7 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-9 + (15 * σ)) := by
        calc
          0 ≤ 255*((12/17)-σ)+270*(σ-(7/10)) := by positivity
          _ = (-9 + (15 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  pm_8335
  ·
    have hl : (12/17) ≤ σ := by linarith
    have hh : σ ≤ (5/7) := by linarith
    apply density_weaken (Montgomery.RationalMoment.two_term_density_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-3 + (8 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (6:ℝ)/(-3 + (8 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-63 + (90 * σ)) := by
        calc
          0 ≤ 63*((5/7)-σ)+153*(σ-(12/17)) := by positivity
          _ = (-63 + (90 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  pm_8336
  ·
    have hl : (5/7) ≤ σ := by linarith
    have hh : σ ≤ (113/153) := by linarith
    apply density_weaken (Montgomery.RationalMoment.adjacent_density_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1 + (9 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (12:ℝ)/(-1 + (9 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-51 + (75 * σ)) := by
        calc
          0 ≤ (1377/13)*((113/153)-σ)+(2352/13)*(σ-(5/7)) := by positivity
          _ = (-51 + (75 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  pm_8337
  ·
    have hl : (113/153) ≤ σ := by linarith
    have hh : σ ≤ (3/4) := by linarith
    apply density_weaken (Montgomery.RationalMoment.third_density_segment (by linarith) (by linarith) _hε)
    have hd1 : 0 < (7 + (153 * σ)) := by linarith
    have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
    have hA : (255:ℝ)/(7 + (153 * σ)) ≤ 15/(3 + (5 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-660 + (1020 * σ)) := by
        calc
          0 ≤ 8160*((3/4)-σ)+9180*(σ-(113/153)) := by positivity
          _ = (-660 + (1020 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (3/4) ≤ σ := by linarith
  have hh : σ ≤ (19/25) := by linarith
  pm_2861
  have hd2 : (0:ℝ) < (3 + (5 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 15/(3 + (5 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-9 + (15 * σ)) := by
      calc
        0 ≤ 225*((19/25)-σ)+240*(σ-(3/4)) := by positivity
        _ = (-9 + (15 * σ)) := by ring
    nlinarith only [hc]
  pm_2859
  convert hp using 1 <;> ring
set_option hygiene false in
macro "pf_103" x1:term:max x2:term:max x3:term:max x4:term:max x5:term:max x6:term:max x7:term:max x8:term:max x9:term:max x10:term:max : tactic => `(tactic| (
  by_cases hz : (7/8 : ℝ) < σ
  · exact density_of_actual_zero hz
  have hright : σ ≤ (7/8 : ℝ) := le_of_not_gt hz
  have hl : ($x1:term/$x2:term) ≤ σ := by linarith
  have hh : σ ≤ ($x3:term/$x4:term) := by linarith
  apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
  have hd1 : 0 < (2 * σ) := by linarith
  have hd2 : (0:ℝ) < (-$x5:term + (($x6:term) * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ $x7:term/(-$x5:term + (($x6:term) * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ ($x8:term + (-($x8:term) * σ)) := by
      calc
        0 ≤ ($x9:term)*(($x3:term/$x4:term)-σ)+($x10:term)*(σ-($x1:term/$x2:term)) := by positivity
        _ = ($x8:term + (-($x8:term) * σ)) := by ring
    nlinarith only [hc]
  have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
  convert hp using 1 <;> ring))
section
variable {σ ε : ℝ}
include σ ε
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_3 (_hlo : (19/25) ≤ σ)
    (_hhi : σ < (127/167)) (_hε : 0 < ε) :
    DensityBound σ ((9 + (-9 * σ)) / (-2 + (8 * σ))) ε := by pf_103 19 25 127 167 2 8 9 6 3006 3000
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_4 (_hlo : (127/167) ≤ σ)
    (_hhi : σ < (13/17)) (_hε : 0 < ε) :
    DensityBound σ ((15 + (-15 * σ)) / (-3 + (13 * σ))) ε := by
  pm_2860
  have hl : (127/167) ≤ σ := by linarith
  have hh : σ ≤ (13/17) := by linarith
  pm_2861
  have hd2 : (0:ℝ) < (-3 + (13 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 15/(-3 + (13 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (9 + (-9 * σ)) := by
      calc
        0 ≤ 510*((13/17)-σ)+501*(σ-(127/167)) := by positivity
        _ = (9 + (-9 * σ)) := by ring
    nlinarith only [hc]
  pm_2859
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_5 (_hlo : (13/17) ≤ σ)
    (_hhi : σ < (17/22)) (_hε : 0 < ε) :
    DensityBound σ ((6 + (-6 * σ)) / (-1 + (5 * σ))) ε := by pf_103 13 17 17 22 1 5 6 3 88 85
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_6 (_hlo : (17/22) ≤ σ)
    (_hhi : σ < (41/53)) (_hε : 0 < ε) :
    DensityBound σ ((2 + (-2 * σ)) / (-6 + (9 * σ))) ε := by
  pm_2860
  have hl : (17/22) ≤ σ := by linarith
  have hh : σ ≤ (41/53) := by linarith
  pm_2861
  have hd2 : (0:ℝ) < (-6 + (9 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 2/(-6 + (9 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (18 + (-23 * σ)) := by
      calc
        0 ≤ 265*((41/53)-σ)+242*(σ-(17/22)) := by positivity
        _ = (18 + (-23 * σ)) := by ring
    nlinarith only [hc]
  pm_2859
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_7 (_hlo : (41/53) ≤ σ)
    (_hhi : σ < (7/9)) (_hε : 0 < ε) :
    DensityBound σ ((9 + (-9 * σ)) / (-1 + (7 * σ))) ε := by
  pm_2860
  have hl : (41/53) ≤ σ := by linarith
  have hh : σ ≤ (7/9) := by linarith
  pm_2861
  have hd2 : (0:ℝ) < (-1 + (7 * σ)) := by linarith
  have hA : (3:ℝ)/(2 * σ) ≤ 9/(-1 + (7 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (3 + (-3 * σ)) := by
      calc
        0 ≤ 162*((7/9)-σ)+159*(σ-(41/53)) := by positivity
        _ = (3 + (-3 * σ)) := by ring
    nlinarith only [hc]
  pm_2859
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_tty_8 (_hlo : (7/9) ≤ σ)
    (_hhi : σ < (1867/2347)) (_hε : 0 < ε) :
    DensityBound σ ((9 + (-9 * σ)) / (-8 + (16 * σ))) ε := by
  pm_2860
  by_cases hc0 : σ ≤ (29359/37574)
  ·
    have hl : (7/9) ≤ σ := by linarith
    have hh : σ ≤ (29359/37574) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7 + (11 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-8 + (16 * σ)) := by linarith
    have hA : (3:ℝ)/(-7 + (11 * σ)) ≤ 9/(-8 + (16 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-39 + (51 * σ)) := by
        calc
          0 ≤ (225444/1213)*((29359/37574)-σ)+(287307/1213)*(σ-(7/9)) := by positivity
          _ = (-39 + (51 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (1015/1294)
  ·
    have hl : (29359/37574) ≤ σ := by linarith
    have hh : σ ≤ (1015/1294) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1283 + (4870 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-8 + (16 * σ)) := by linarith
    have hA : (4744:ℝ)/(-1283 + (4870 * σ)) ≤ 9/(-8 + (16 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (26405 + (-32074 * σ)) := by
        calc
          0 ≤ (13769454/31)*((1015/1294)-σ)+(12775160/31)*(σ-(29359/37574)) := by positivity
          _ = (26405 + (-32074 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (353/447)
  ·
    have hl : (1015/1294) ≤ σ := by linarith
    have hh : σ ≤ (353/447) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_third (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1693 + (6354 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-8 + (16 * σ)) := by linarith
    have hA : (6154:ℝ)/(-1693 + (6354 * σ)) ≤ 9/(-8 + (16 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (33995 + (-41278 * σ)) := by
        calc
          0 ≤ 303960*((353/447)-σ)+262682*(σ-(1015/1294)) := by positivity
          _ = (33995 + (-41278 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  have hl : (353/447) ≤ σ := by linarith
  have hh : σ ≤ (1867/2347) := by linarith
  apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
  have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
  have hd2 : (0:ℝ) < (-8 + (16 * σ)) := by linarith
  have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 9/(-8 + (16 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (20671 + (-25088 * σ)) := by
      calc
        0 ≤ (900949931/6058)*((1867/2347)-σ)+(748966827/6058)*(σ-(353/447)) := by positivity
        _ = (20671 + (-25088 * σ)) := by ring
    nlinarith only [hc]
  pm_2859
  convert hp using 1 <;> ring
end
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_kerr6 {σ ε : ℝ} (_hlo : (23/29) ≤ σ)
    (_hhi : σ ≤ 1) (_hε : 0 < ε) :
    DensityBound σ ((3 + (-3 * σ)) / (2 * σ)) ε := by
  pm_2860
  by_cases hc0 : σ ≤ (467/586)
  ·
    have hl : (23/29) ≤ σ := by linarith
    have hh : σ ≤ (467/586) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3195 + (4244 * σ)) := by
        calc
          0 ≤ (2904802/65)*((467/586)-σ)+(3180662/65)*(σ-(23/29)) := by positivity
          _ = (-3195 + (4244 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc1 : σ ≤ (4/5)
  ·
    have hl : (467/586) ≤ σ := by linarith
    have hh : σ ≤ (4/5) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1893 + (2510 * σ)) := by
        calc
          0 ≤ (314360/9)*((4/5)-σ)+(336950/9)*(σ-(467/586)) := by positivity
          _ = (-1893 + (2510 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc2 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1893 + (2510 * σ)) := by
        calc
          0 ≤ (205850/13)*((289/358)-σ)+(238480/13)*(σ-(4/5)) := by positivity
          _ = (-1893 + (2510 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc3 : σ ≤ (163/198)
  ·
    have hl : (289/358) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-519 + (686 * σ)) := by
        calc
          0 ≤ 2178*((163/198)-σ)+2864*(σ-(289/358)) := by positivity
          _ = (-519 + (686 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (7873/9370)
  ·
    have hl : (163/198) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-33609 + (43922 * σ)) := by
        calc
          0 ≤ 149920*((7873/9370)-σ)+193842*(σ-(163/198)) := by positivity
          _ = (-33609 + (43922 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc5 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-1396527 + (1818960 * σ)) := by
        calc
          0 ≤ 13950750*((2018/2375)-σ)+15769710*(σ-(7873/9370)) := by positivity
          _ = (-1396527 + (1818960 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc6 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-3645 + (4716 * σ)) := by
        calc
          0 ≤ (3868042266/31949)*((1959705/2298302)-σ)+(4018713750/31949)*(σ-(2018/2375)) := by positivity
          _ = (-3645 + (4716 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc7 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-772245 + (991724 * σ)) := by
        calc
          0 ≤ (213486426657/10778)*((6482825/7570038)-σ)+(224175227929/10778)*(σ-(1959705/2298302)) := by positivity
          _ = (-772245 + (991724 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  pm_7085 hc8
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (2 * σ) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 3/(2 * σ) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (-22870785 + (29189586 * σ)) := by
        calc
          0 ≤ 218098322*((2905/3354)-σ)+247287908*(σ-(6482825/7570038)) := by positivity
          _ = (-22870785 + (29189586 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  pm_2862
  have hd2 : (0:ℝ) < (2 * σ) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 3/(2 * σ) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (-3045 + (3882 * σ)) := by
      calc
        0 ≤ (608160/17)*((7/8)-σ)+(674154/17)*(σ-(2905/3354)) := by positivity
        _ = (-3045 + (3882 * σ)) := by ring
    nlinarith only [hc]
  pm_2859
  convert hp using 1 <;> ring
/-- Exact published-source density conclusion, supplied by native project domination and strict actual zero-freeness. No new mathematics or claim to reprove the original published route. -/
theorem source_extra_baseline_full_hb {σ ε : ℝ} (_hlo : (7/10) < σ)
    (_hhi : σ ≤ 1) (_hε : 0 < ε) :
    DensityBound σ ((3 + (-3 * σ)) / (-7 + (10 * σ))) ε := by
  pm_2860
  pm_8334
  ·
    have hl : (7/10) ≤ σ := by linarith
    have hh : σ ≤ (12/17) := by linarith
    apply density_weaken (Montgomery.Refined.refined_density_middle (by linarith) (by linarith) _hε)
    have hd1 : 0 < (3 + (7 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (18:ℝ)/(3 + (7 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (135 + (-159 * σ)) := by
        calc
          0 ≤ 4029*((12/17)-σ)+3870*(σ-(7/10)) := by positivity
          _ = (135 + (-159 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  pm_8335
  ·
    have hl : (12/17) ≤ σ := by linarith
    have hh : σ ≤ (5/7) := by linarith
    apply density_weaken (Montgomery.RationalMoment.two_term_density_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-3 + (8 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (6:ℝ)/(-3 + (8 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (33 + (-36 * σ)) := by
        calc
          0 ≤ 903*((5/7)-σ)+867*(σ-(12/17)) := by positivity
          _ = (33 + (-36 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  pm_8336
  ·
    have hl : (5/7) ≤ σ := by linarith
    have hh : σ ≤ (113/153) := by linarith
    apply density_weaken (Montgomery.RationalMoment.adjacent_density_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1 + (9 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (12:ℝ)/(-1 + (9 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (81 + (-93 * σ)) := by
        calc
          0 ≤ (7803/13)*((113/153)-σ)+(6594/13)*(σ-(5/7)) := by positivity
          _ = (81 + (-93 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  pm_8337
  ·
    have hl : (113/153) ≤ σ := by linarith
    have hh : σ ≤ (3/4) := by linarith
    apply density_weaken (Montgomery.RationalMoment.third_density_segment (by linarith) (by linarith) _hε)
    have hd1 : 0 < (7 + (153 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (255:ℝ)/(7 + (153 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (1806 + (-2091 * σ)) := by
        calc
          0 ≤ (160140/7)*((3/4)-σ)+(145503/7)*(σ-(113/153)) := by positivity
          _ = (1806 + (-2091 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc4 : σ ≤ (7/9)
  ·
    have hl : (3/4) ≤ σ := by linarith
    have hh : σ ≤ (7/9) := by linarith
    apply density_weaken (MathCollab.Density.Stronger.stronger_density_bound_native (by linarith) _hε)
    have hd1 : 0 < (2 * σ) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (3:ℝ)/(2 * σ) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (21 + (-24 * σ)) := by
        calc
          0 ≤ 108*((7/9)-σ)+84*(σ-(3/4)) := by positivity
          _ = (21 + (-24 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc5 : σ ≤ (29359/37574)
  ·
    have hl : (7/9) ≤ σ := by linarith
    have hh : σ ≤ (29359/37574) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7 + (11 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (3:ℝ)/(-7 + (11 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (3 * σ) := by
        calc
          0 ≤ (789054/1213)*((29359/37574)-σ)+(792693/1213)*(σ-(7/9)) := by positivity
          _ = (3 * σ) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc6 : σ ≤ (1015/1294)
  ·
    have hl : (29359/37574) ≤ σ := by linarith
    have hh : σ ≤ (1015/1294) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1283 + (4870 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (4744:ℝ)/(-1283 + (4870 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (29359 + (-32830 * σ)) := by
        calc
          0 ≤ (37990546/31)*((1015/1294)-σ)+(36972816/31)*(σ-(29359/37574)) := by positivity
          _ = (29359 + (-32830 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc7 : σ ≤ (353/447)
  ·
    have hl : (1015/1294) ≤ σ := by linarith
    have hh : σ ≤ (353/447) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_third (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1693 + (6354 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (6154:ℝ)/(-1693 + (6354 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (37999 + (-42478 * σ)) := by
        calc
          0 ≤ 879696*((353/447)-σ)+837218*(σ-(1015/1294)) := by positivity
          _ = (37999 + (-42478 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc8 : σ ≤ (467/586)
  ·
    have hl : (353/447) ≤ σ := by linarith
    have hh : σ ≤ (467/586) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fourth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1065 + (3936 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (3782:ℝ)/(-1065 + (3936 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (23279 + (-26012 * σ)) := by
        calc
          0 ≤ 379142*((467/586)-σ)+353130*(σ-(353/447)) := by positivity
          _ = (23279 + (-26012 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc9 : σ ≤ (4/5)
  ·
    have hl : (467/586) ≤ σ := by linarith
    have hh : σ ≤ (4/5) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_right_solid_fifth (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (13283 + (-14834 * σ)) := by
        calc
          0 ≤ (4281800/9)*((4/5)-σ)+(4148294/9)*(σ-(467/586)) := by positivity
          _ = (13283 + (-14834 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc10 : σ ≤ (289/358)
  ·
    have hl : (4/5) ≤ σ := by linarith
    have hh : σ ≤ (289/358) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_first (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-631 + (2282 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (2168:ℝ)/(-631 + (2282 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (13283 + (-14834 * σ)) := by
        calc
          0 ≤ (2534282/13)*((289/358)-σ)+(2341440/13)*(σ-(4/5)) := by positivity
          _ = (13283 + (-14834 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc11 : σ ≤ (163/198)
  ·
    have hl : (289/358) ≤ σ := by linarith
    have hh : σ ≤ (163/198) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.density_dashed_second (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-173 + (606 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (566:ℝ)/(-173 + (606 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (3443 + (-3842 * σ)) := by
        calc
          0 ≤ 21384*((163/198)-σ)+17542*(σ-(289/358)) := by positivity
          _ = (3443 + (-3842 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc12 : σ ≤ (7873/9370)
  ·
    have hl : (163/198) ≤ σ := by linarith
    have hh : σ ≤ (7873/9370) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_cube_row3 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-11203 + (35670 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (31544:ℝ)/(-11203 + (35670 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (187199 + (-208430 * σ)) := by
        calc
          0 ≤ 918260*((7873/9370)-σ)+709830*(σ-(163/198)) := by positivity
          _ = (187199 + (-208430 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc13 : σ ≤ (2018/2375)
  ·
    have hl : (7873/9370) ≤ σ := by linarith
    have hh : σ ≤ (2018/2375) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row4 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-465509 + (1447460 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (1261710:ℝ)/(-465509 + (1447460 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (7435443 + (-8274720 * σ)) := by
        calc
          0 ≤ 51086250*((2018/2375)-σ)+42811530*(σ-(7873/9370)) := by positivity
          _ = (7435443 + (-8274720 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc14 : σ ≤ (1959705/2298302)
  ·
    have hl : (2018/2375) ≤ σ := by linarith
    have hh : σ ≤ (1959705/2298302) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_universal_row5 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-1215 + (3616 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (3066:ℝ)/(-1215 + (3616 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (17817 + (-19812 * σ)) := by
        calc
          0 ≤ (10500941838/31949)*((1959705/2298302)-σ)+(9867968250/31949)*(σ-(2018/2375)) := by positivity
          _ = (17817 + (-19812 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  by_cases hc15 : σ ≤ (6482825/7570038)
  ·
    have hl : (1959705/2298302) ≤ σ := by linarith
    have hh : σ ≤ (6482825/7570038) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row6 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-257415 + (729216 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (597962:ℝ)/(-257415 + (729216 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (3413489 + (-3791972 * σ)) := by
        calc
          0 ≤ (2621084022291/53890)*((6482825/7570038)-σ)+(2416734651211/53890)*(σ-(1959705/2298302)) := by positivity
          _ = (3413489 + (-3791972 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  pm_7085 hc16
  ·
    have hl : (6482825/7570038) ≤ σ := by linarith
    have hh : σ ≤ (2905/3354) := by linarith
    apply density_weaken (Montgomery.RationalMoment.RightDetector.Physical.density_sharp_row7 (by linarith) (by linarith) _hε)
    have hd1 : 0 < (-7623595 + (20732766 * σ)) := by linarith
    have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
    have hA : (16504356:ℝ)/(-7623595 + (20732766 * σ)) ≤ 3/(-7 + (10 * σ)) := by
      apply (div_le_div_iff₀ hd1 hd2).2
      have hc : 0 ≤ (92659707 + (-102845262 * σ)) := by
        calc
          0 ≤ (2351222198/5)*((2905/3354)-σ)+(1836995888/5)*(σ-(6482825/7570038)) := by positivity
          _ = (92659707 + (-102845262 * σ)) := by ring
      nlinarith only [hc]
    have hp := mul_le_mul_of_nonneg_right hA (by linarith : 0 ≤ 1-σ)
    convert hp using 1 <;> ring
  pm_2862
  have hd2 : (0:ℝ) < (-7 + (10 * σ)) := by linarith
  have hA : (2172:ℝ)/(-1015 + (2742 * σ)) ≤ 3/(-7 + (10 * σ)) := by
    apply (div_le_div_iff₀ hd1 hd2).2
    have hc : 0 ≤ (12159 + (-13494 * σ)) := by
      calc
        0 ≤ (903552/17)*((7/8)-σ)+(674154/17)*(σ-(2905/3354)) := by positivity
        _ = (12159 + (-13494 * σ)) := by ring
    nlinarith only [hc]
  pm_2859
  convert hp using 1 <;> ring
end Montgomery.LiteratureDensity
