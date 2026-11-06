module

public import Mathlib.Tactic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

public section

namespace HordijkSteelThreshold

open MeasureTheory

/-- Expected bad mass is the sum of individual bad probabilities. No
independence of contour events or vertex indicators is assumed. -/
theorem lintegral_bad_card {Ω X : Type*} [Fintype Ω] [Fintype X]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) (bad : Ω → Finset X) :
    (∫⁻ ω, ((bad ω).card : ENNReal) ∂μ) = ∑ x : X, μ {ω | x ∈ bad ω} := by
  have he ω : ((bad ω).card : ENNReal) = ∑ x : X, {ω | x ∈ bad ω}.indicator 1 ω := by
    simp [Set.indicator]
  simp_rw [he, lintegral_finsetSum _ fun _ _ => measurable_of_finite _]
  simp [(Set.toFinite _).measurableSet]

end HordijkSteelThreshold
