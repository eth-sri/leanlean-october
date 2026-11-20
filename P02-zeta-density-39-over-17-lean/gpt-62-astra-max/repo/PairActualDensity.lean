module
public import DensityStrip.Pair
public import QuadraticPolynomialCount

@[expose] public section
set_option autoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
namespace Montgomery.RationalMoment.RightDetector
open MathCollab.Density.Stronger MathCollab.Density TaoTrudgianYang2025

/-- Actual zeta zeros from a genuine analytic pair, with every detector and
tail input discharged. The two exact exponent budgets are numerical. -/
theorem density_of_pair_tail_window {k l σ a ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hw : QuadraticWindow σ a)
    (hthreshold : 1/8 < (3*a/4)*(σ-1/2))
    (hfirst : 1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hsecond : 1+l/k-(4+(2+4*l)/k)*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  have ha : 0 < a := by linarith [hw.a_low]
  have hmargin := mul_pos ha (show 0 < 4*σ-3 by linarith [hw.sigma_low])
  apply DensityStrip.pair_density hpair hk ⟨hw.sigma_low,hw.sigma_high,hw.a_low,hw.a_high,hthreshold⟩ hfirst hsecond (B:=51) (by norm_num)
    (c:=min ((1-3*a/2)/2) (a*(4*σ-3)/10)) (lt_min (by linarith [hw.a_high]) (by positivity)) _ hε
  intro e he hec
  obtain ⟨C,hC,h⟩ := quadratic_polynomial_count_loss hw he (le_min_iff.mp hec).1 (by linarith only [(le_min_iff.mp hec).2,he])
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with T ht
  intro N Q b W _ hlo hhi hb
  exact ht Q T hlo hhi b hb W
end Montgomery.RationalMoment.RightDetector
