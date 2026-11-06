module
public import TaoTrudgianYang2025.BProcessBaseline
public import TaoTrudgianYang2025.BetaStationaryMain
import WeylPort.Analytic.RealLaplace

@[expose] public section

/-!
# Source-facing partial summation of the actual stationary main block

The real curvature weight is derived from the original model phase.
Its finite variation controls the literal canonical prefix maximum.
Neither variation nor a weighted exponential-sum estimate is assumed.
The approximation of Fourier integrals by these main terms remains separate.
-/

noncomputable section

open Set Expdb
open scoped FourierTransform BigOperators

namespace TaoTrudgianYang2025
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

def modelPhaseStationaryBlock (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) : ℂ :=
  ∑ r ∈ Finset.Icc a (a+L), modelPhaseStationaryMainTerm F T N r

theorem modelPhaseStationaryBlock_eq_range (F : ℝ → ℝ) (T N : ℝ) (a L : ℕ) :
    modelPhaseStationaryBlock F T N a L =
      ∑ i ∈ Finset.range (L+1), modelPhaseStationaryMainTerm F T N ((a : ℝ)+i) := by
  pm_7101 modelPhaseStationaryBlock
  grind

end TaoTrudgianYang2025
