module
public import LaterPairs.PhysicalPairLongZeroCount
public import LaterPairs.PhysicalSharpActualDensity
public import RetunedActualDensity

@[expose] public section
set_option autoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density TaoTrudgianYang2025

/-- Actual zeta zeros from a genuine analytic pair, with every detector and
tail input discharged. The two exact exponent budgets are numerical. -/
theorem density_of_pair_tail_window {k l σ a ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k) (_hlog : 2+4*l/k ≤ 7)
    (hw : QuadraticWindow σ a) (_hsigma : 7/9 ≤ σ)
    (hthreshold : 1/8 < (3*a/4)*(σ-1/2))
    (hfirst : 1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hsecond : 1+l/k-(4+(2+4*l)/k)*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) :=
  Physical.density_of_pair_window (loss := 52) hpair hk
    ⟨hw.sigma_low, hw.sigma_high, hw.a_low, hw.a_high, hthreshold⟩ hfirst hsecond hε (by norm_num)
    fun _ hη _ ha hg => smoothShortZeroCount_bound hw hη ha hg

end Montgomery.RationalMoment.RightDetector
