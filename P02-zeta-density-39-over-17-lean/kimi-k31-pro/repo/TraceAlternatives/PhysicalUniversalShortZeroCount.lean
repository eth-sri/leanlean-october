module
public import LaterPairs.PhysicalSharpShortZeroCount
public import TraceAlternatives.UniversalPolynomialCountWindows

@[expose] public section
open Real Complex Filter MeasureTheory Finset Set
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density GuthMaynard.Improvement

/-- All actual short-detected zeros with analytic multiplicity, using the universal trace. -/
theorem smoothShortZeroCount_universal_bound {σ a η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hc : UniversalCountWindow σ a) (hη : 0 < η)
    (hηsmall : η ≤ 1/1800) (hηa : η ≤ (1-3*a/2)/2) (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothShortZeroCount η σ a δ T:ℝ) ≤ C*T^(3*a*(1-σ)+145*η) := by
  obtain ⟨C,T₀,hC,hT₀,hquad⟩ := universal_polynomial_count_window_loss hc hη hηsmall hηa
  simpa only [show (145:ℝ)=144+1 by norm_num] using
    smoothShortZeroCount_of_window_loss (r := 144) hw hη δ ⟨C,T₀,hC,hT₀,hquad⟩

end Montgomery.RationalMoment.RightDetector.Physical
