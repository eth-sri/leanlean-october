module
public import RetunedLongMeanCover
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
  obtain ⟨C,T₀,hC,_,hcount⟩ := universal_polynomial_count_window_loss hc hη hηsmall hηa
  have hLV : ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ShortWindowCount σ a η T (C*T^(3*a*(1-σ)+144*η)) := by
    refine ⟨C,hC,?_⟩
    filter_upwards [eventually_ge_atTop T₀] with T hT
    intro N t₀
    exact hcount T t₀ N hT
  simpa only [add_assoc, show 144*η+η=145*η by ring] using
    smoothShortZeroCount_of_count hw.sigma_low.le (by linarith [hw.a_low]) hw.a_high hη δ hLV

end Montgomery.RationalMoment.RightDetector.Physical
