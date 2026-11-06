module

public import proofs.HordijkSteelThreshold.ReversibleEscape
public import proofs.HordijkSteelThreshold.SprinkledSeedLowerBound

public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval

theorem reversible_escape_probability_tendsto
    (μ : Measure InfiniteSplitEnvironment) [IsFiniteMeasure μ] (L : ℕ) :
    Filter.Tendsto (μ $ reversibleEscapeEvent L ·) Filter.atTop
      (nhds $ μ {field | ReversibleUnbounded L field}) := by
  have ht := tendsto_measure_iInter_atTop (μ := μ)
    (fun K => (measurableSet_reversibleEscapeEvent L K).nullMeasurableSet)
    (reversibleEscapeEvent_antitone L) ⟨0, measure_ne_top _ _⟩
  rw [reversibleEscapeEvent_inter] at ht
  aesop

end HordijkSteelThreshold
