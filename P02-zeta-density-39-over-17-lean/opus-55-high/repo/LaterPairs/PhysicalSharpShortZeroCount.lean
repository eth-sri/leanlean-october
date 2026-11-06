module
public import LaterPairs.PhysicalLongMeanCover
public import RetunedShortZeroCount
public import DensityEnergyGM.SharpPolynomialCountWindows
import WeylPort.Analytic.RealLaplace

public section

open Real Complex Filter MeasureTheory Finset Set
open scoped Topology
set_option maxHeartbeats 2400000
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density GuthMaynard.Improvement

/-- All actual short-detected zeros with analytic multiplicity, using the
proved sharp trace and full energy. The exact perturbation loss is73eta. -/
theorem smoothShortZeroCount_sharp_bound {σ a η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hc : SharpCountWindow σ a) (hη : 0 < η)
    (hηa : η ≤ (1-3*a/2)/2) (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothShortZeroCount η σ a δ T:ℝ) ≤ C*T^(3*a*(1-σ)+73*η) := by pm_2699 sharp_polynomial_count_window_loss

end Montgomery.RationalMoment.RightDetector.Physical
