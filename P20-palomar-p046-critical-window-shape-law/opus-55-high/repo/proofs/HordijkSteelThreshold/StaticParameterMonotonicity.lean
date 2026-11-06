module

public import proofs.HordijkSteelThreshold.BernoulliSprinkling
public import Mathlib.Probability.ProductMeasure
public import proofs.HordijkSteelThreshold.RandomBaseSprinkling

public section

namespace HordijkSteelThreshold
open Classical MeasureTheory RAF.Polymer RAF.Concrete unitInterval

theorem exists_sprinkling_increment {a c : I} (hac : a ≤ c) :
    ∃ b : I, sprinklingParameter a b = c := by
  by_cases he : a = c
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    rw [sprinklingParameter_value]
    simp_all
  · have hltI := lt_of_le_of_ne hac he
    have hlt : (a : ℝ) < c := hltI
    have hd : 0 < 1-(a : ℝ) := by grind
    let b : I := ⟨(c-a)/(1-a), by
      constructor
      · positivity
      · apply (div_le_one hd).mpr
        have hc := c.property.2
        linarith⟩
    refine ⟨b, ?_⟩
    apply Subtype.ext
    rw [sprinklingParameter_value]
    grind

end HordijkSteelThreshold
