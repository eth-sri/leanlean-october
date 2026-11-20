module
public import QuadraticPolynomialCount
public import DensityWindowBudgets

@[expose] public section

open MeasureTheory Set Filter
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density

/-- The literal positive excess of the actual critical-line zeta norm. -/
def criticalExcess (v t : ℝ) : ℝ := max (zetaMomentCriticalNorm t-v) 0

theorem criticalExcess_nonneg (v t : ℝ) : 0 ≤ criticalExcess v t := le_max_right _ _

theorem criticalExcess_continuous (v : ℝ) : Continuous (criticalExcess v) :=
  (continuous_zetaMomentCriticalNorm.sub continuous_const).max continuous_const

theorem critical_norm_le_threshold_add_excess (v t : ℝ) :
    zetaMomentCriticalNorm t ≤ v+criticalExcess v t := by
  have h := le_max_left (zetaMomentCriticalNorm t-v) 0
  dsimp only [criticalExcess]
  linarith







end Montgomery.RationalMoment.RightDetector
