module
public import LaterPairs.PhysicalExcessReduction
public import LaterPairs.PairPhysicalExcess
public import DetectorPowerRange
import WeylPort.Analytic.RealLaplace

public section
open Real Filter MeasureTheory
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger
open TaoTrudgianYang2025

/-- The actual complementary zeros obey the two native pair-tail budgets.
The numerical slack accounts explicitly for the detector denominator and logarithm. -/
theorem smoothLongZeroCount_pair_tail_general {k l σ a δ η q ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hw : PhysicalDetectorWindow σ a) 
    (hδ : 0 < δ) (hδcap : δ ≤ 1/8) (hη : 0 < η) (hε : 0 < ε)
    (hq : 1/8 < q) (hmargin : q+δ/2 < (3*a/4)*(σ-1/2))
    (hfirst : 1-6*q ≤ 3*a*(1-σ)+ε/2)
    (hsecond : 1+l/k-(4+(2+4*l)/k)*q ≤ 3*a*(1-σ)+ε/2) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothLongZeroCount η σ a δ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  pm_642
  pm_358 hξ ξ
  pm_705
  pm_270
  pm_1604
  obtain ⟨Cm,D,hCm,hD,hraw⟩ := smoothLongZeroCount_excess_reduction hw hδ hδcap hη
  pm_114 A hA htail hpair.critical_physical_excess_general hk hξ hquarter
  pm_171
  pm_4312
  pm_496
  pm_4366
  pm_78
  pm_58
end Montgomery.RationalMoment.RightDetector.Physical
