module
public import LaterPairs.PhysicalSharpShortZeroCount
public import TraceAlternatives.CubePolynomialCountWindows

@[expose] public section
open Real Complex Filter MeasureTheory Finset Set
open scoped BigOperators Topology
set_option autoImplicit false
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density GuthMaynard.Improvement

/-- All actual short-detected zeros with analytic multiplicity, using the cube trace. -/
theorem smoothShortZeroCount_cube_bound {σ a η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hc : CubeCountWindow σ a) (hη : 0 < η)
    (hηa : η ≤ (1-3*a/2)/2) (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothShortZeroCount η σ a δ T:ℝ) ≤ C*T^(3*a*(1-σ)+73*η) := by
  obtain ⟨C,hC,hquad⟩ := cube_polynomial_count_window_loss hc hη hηa
  simpa only [show (73:ℝ)=72+1 by norm_num] using
    smoothShortZeroCount_of_window_loss (r := 72) hw hη δ ⟨C,2,hC,le_rfl,hquad⟩

end Montgomery.RationalMoment.RightDetector.Physical
