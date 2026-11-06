module
import Mathlib
public import NativeBHBPeakTails
public import PairActualDensity
public import DashedInitialParameters

@[expose] public section

namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density TaoTrudgianYang2025

/-- The first full dashed target follows from the proved quadratic window
and the native BHB7 tail on this interval. -/
theorem density_dashed_first {σ ε : ℝ}
    (hl : 4/5 ≤ σ) (hr : σ ≤ 289/358) (hε : 0 < ε) :
    MathCollab.Density.ZetaBound σ ((2168*(1-σ)/(2282*σ-631)+ε)) := by
  have hw := dashed_first_quadratic_window hl hr
  have hb := dashed_first_tail_budgets hl hr
  have hh := density_of_pair_tail_window exponentPair_BHB7 (by norm_num) (by norm_num)
    hw (by linarith : (7:ℝ)/9 ≤ σ) hb.1 hb.2.1 hb.2.2 hε
  grind

/-- The second full dashed target uses native BHB6, with no energy or trace premise. -/
theorem density_dashed_second {σ ε : ℝ}
    (hl : 289/358 ≤ σ) (hr : σ ≤ 163/198) (hε : 0 < ε) :
    MathCollab.Density.ZetaBound σ ((566*(1-σ)/(606*σ-173)+ε)) := by
  have hw := dashed_second_quadratic_window hl hr
  have hb := dashed_second_tail_budgets hl hr
  have hh := density_of_pair_tail_window exponentPair_BHB6 (by norm_num) (by norm_num)
    hw (by linarith : (7:ℝ)/9 ≤ σ) hb.1 hb.2.1 hb.2.2 hε
  grind


