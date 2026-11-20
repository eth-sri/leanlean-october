module
public import LaterPairs.PhysicalPairLongZeroCount
public import TraceAlternatives.PhysicalCubeShortZeroCount
public import LaterPairs.PhysicalSharpActualDensity
public import RetunedActualDensity

@[expose] public section
set_option autoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density TaoTrudgianYang2025

/-- Actual zeta zeros from a genuine analytic pair, with every detector and
tail input discharged. The two exact exponent budgets are numerical. -/
theorem density_of_pair_cube_window {k l σ a ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hw : PhysicalDetectorWindow σ a) (hc : CubeCountWindow σ a)
    (hfirst : 1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hsecond : 1+l/k-(4+(2+4*l)/k)*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) :=
  density_of_pair_window (loss := 73) hpair hk hw hfirst hsecond hε (by norm_num)
    fun _ hη _ ha _ => smoothShortZeroCount_cube_bound hw hc hη ha

end Montgomery.RationalMoment.RightDetector.Physical
