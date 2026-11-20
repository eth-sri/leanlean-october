module
public import RetunedLongMeanCover
public import RetunedShortZeroCount
public import TraceAlternatives.CubePolynomialCountWindows

@[expose] public section

open Real Complex Filter MeasureTheory Finset Set
open scoped BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace Montgomery.RationalMoment.RightDetector.Physical
open MathCollab.Density.Stronger MathCollab.Density GuthMaynard.Improvement

/-- All actual short-detected zeros with analytic multiplicity, using the
proved sharp trace and full energy. The exact perturbation loss is73eta. -/
theorem smoothShortZeroCount_cube_bound {σ a η : ℝ}
    (hw : PhysicalDetectorWindow σ a) (hc : CubeCountWindow σ a) (hη : 0 < η)
    (hηa : η ≤ (1-3*a/2)/2) (δ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      (smoothShortZeroCount η σ a δ T:ℝ) ≤ C*T^(3*a*(1-σ)+73*η) := by
  obtain ⟨C,hC,hcount⟩ := cube_polynomial_count_window_loss hc hη hηa
  have hLV : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ShortWindowCount σ a η T (C*T^(3*a*(1-σ)+72*η)) := by
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_ge_atTop (2:ℝ)] with T hT
    intro N t₀
    exact hcount T t₀ N hT
  simpa only [add_assoc, show 72*η+η=73*η by ring] using
    smoothShortZeroCount_of_count hw.sigma_low.le (by linarith [hw.a_low]) hw.a_high hη δ hLV

end Montgomery.RationalMoment.RightDetector.Physical
