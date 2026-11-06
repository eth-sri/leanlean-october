module
public import LaterPairs.PhysicalLongMeanCover
public import RetunedShortZeroCount
public import TraceAlternatives.UniversalPolynomialCountWindows

@[expose] public section

open Real Complex Filter MeasureTheory Finset Set
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density GuthMaynard.Improvement

/-- All actual short-detected zeros with analytic multiplicity, using the
proved sharp trace and full energy. The exact perturbation loss is145eta. -/
theorem smoothShortZeroCount_universal_bound {σ a η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hc : UniversalCountWindow σ a) (hη : 0 < η)
    (hηsmall : η ≤ 1/1800) (hηa : η ≤ (1-3*a/2)/2) (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothShortZeroCount η σ a δ T:ℝ) ≤ C*T^(3*a*(1-σ)+145*η) := by
  obtain ⟨C, T₀, hC, _, hquad⟩ := universal_polynomial_count_window_loss hc hη hηsmall hηa
  simpa only [show (144:ℝ)+1 = 145 by norm_num] using
    smoothShortZeroCount_of_poly_loss (m := 144) hw hη δ
      ⟨C, hC, (eventually_ge_atTop T₀).mono fun T hT N => hquad T T N hT⟩

