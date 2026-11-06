module
public import NativeBHBPeakTails
public import PairActualDensity
public import DashedInitialParameters
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density TaoTrudgianYang2025

/-- The first full dashed target follows from the proved quadratic window
and the native BHB7 tail on this interval. -/
theorem density_dashed_first {σ ε : ℝ}
    (hl : 4/5 ≤ σ) (hr : σ ≤ 289/358) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(2168*(1-σ)/(2282*σ-631)+ε) := by
  pm_111 hw dashed_first_quadratic_window hl hr hb dashed_first_tail_budgets
  pm_1243 exponentPair_BHB7
  have he : 3*(2168/(6846*σ-1893))*(1-σ)=2168*(1-σ)/(2282*σ-631) := by
    rw [show 6846*σ-1893=3*(2282*σ-631) by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  grind

/-- The second full dashed target uses native BHB6, with no energy or trace premise. -/
theorem density_dashed_second {σ ε : ℝ}
    (hl : 289/358 ≤ σ) (hr : σ ≤ 163/198) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(566*(1-σ)/(606*σ-173)+ε) := by
  pm_111 hw dashed_second_quadratic_window hl hr hb dashed_second_tail_budgets
  pm_1243 exponentPair_BHB6
  have he : 3*(566/(1818*σ-519))*(1-σ)=566*(1-σ)/(606*σ-173) := by
    rw [show 1818*σ-519=3*(606*σ-173) by ring]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  grind

end Montgomery.RationalMoment.RightDetector
