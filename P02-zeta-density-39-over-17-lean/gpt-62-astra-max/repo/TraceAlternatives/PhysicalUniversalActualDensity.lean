module
public import DensityStrip.Pair
public import TraceAlternatives.UniversalPolynomialCountWindows

@[expose] public section
set_option autoImplicit false
noncomputable section
open Real Filter MeasureTheory Set
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density TaoTrudgianYang2025

/-- Actual zeta zeros from a genuine analytic pair, with every detector and
tail input discharged. The two exact exponent budgets are numerical. -/
theorem density_of_pair_universal_window {k l σ a ε : ℝ}
    (hpair : ExponentPair k l) (hk : 0 < k)
    (hw : PhysicalDetectorWindow σ a) (hc : UniversalCountWindow σ a)
    (hfirst : 1-6*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hsecond : 1+l/k-(4+(2+4*l)/k)*((3*a/4)*(σ-1/2)) ≤ 3*a*(1-σ))
    (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ T : ℝ,2 ≤ T →
      (zetaDensityCount σ T:ℝ) ≤ C*T^(3*a*(1-σ)+ε) := by
  apply DensityStrip.pair_density hpair hk hw hfirst hsecond (B:=144) (by norm_num)
    (c:=min (1/1800) ((1-3*a/2)/2)) (lt_min (by norm_num) (by linarith [hw.a_high])) _ hε
  intro e he hec
  obtain ⟨C,T₀,hC,_,h⟩ := universal_polynomial_count_window_loss hc he (le_min_iff.mp hec).1 (le_min_iff.mp hec).2
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop T₀] with T ht
  intro N Q b W _ hlo hhi hb
  exact h T T Q ht hlo hhi b hb W
end Montgomery.RationalMoment.RightDetector.Physical
