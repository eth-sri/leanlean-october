module
public import LaterPairs.PhysicalSharpActualDensity
public import TraceAlternatives.PhysicalUniversalShortZeroCount

@[expose] public section
set_option autoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density TaoTrudgianYang2025

/-- Actual zeta zeros from a genuine analytic pair with universal short-window input. -/
theorem density_of_pair_universal_window {k l σ a ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hw : PhysicalDetectorWindow σ a) (hc : UniversalCountWindow σ a)
    (hfirst : 1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hsecond : 1+l/k-(4+(2+4*l)/k)*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  apply density_of_pair_with_short_bound hpair hk hw hfirst hsecond hε (by norm_num : (0:ℝ) < 145)
  intro η hη hηsmall hηa δ
  exact smoothShortZeroCount_universal_bound hw hc hη (by linarith) (by linarith) δ

end Montgomery.RationalMoment.RightDetector.Physical
