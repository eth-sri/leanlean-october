module

public import proofs.HordijkSteelThreshold.AmbientIndependence

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval

variable (a b : I)

def sprinklingParameter  : I := σ $ (σ a) * (σ b)

theorem sprinklingParameter_value  :
    (sprinklingParameter a b : ℝ) = (a : ℝ) + (1-(a : ℝ))*(b : ℝ) := by
  change 1-((1-a)*(1-(b : ℝ))) = _
  ring

/-- Exact law of the union of two independent Bernoulli coordinates. -/
theorem ambientCoordLaw_union  :
    ((ambientCoordLaw a).prod $ ambientCoordLaw b).map (fun p : Prop × Prop => p.1 ∨ p.2) =
      ambientCoordLaw (sprinklingParameter a b) := by
  let μ := ((ambientCoordLaw a).prod $ ambientCoordLaw b).map
    (fun p : Prop × Prop => p.1 ∨ p.2)
  have hf : μ {False} = ambientCoordLaw (sprinklingParameter a b) {False} := by
    rw [ Measure.map_apply (measurable_of_finite _)
      (MeasurableSet.singleton False)]
    have he : (fun p : Prop × Prop => p.1 ∨ p.2) ⁻¹' {False} =
        ({False}) ×ˢ {False} := by grind
    rw [he, Measure.prod_prod]
    simp [ambientCoordLaw, sprinklingParameter]
    rfl
  have ht : μ {True} = ambientCoordLaw (sprinklingParameter a b) {True} := by
    have he : ({True}) = ({False} : Set Prop)ᶜ := by simp_all
    rw [he, measure_compl (MeasurableSet.singleton False) $ measure_ne_top _ _,
      measure_compl (MeasurableSet.singleton False) $ measure_ne_top _ _, hf]
    simp
  apply Measure.ext_of_singleton
  intro P
  by_cases h : P
  · grind
  grind

end HordijkSteelThreshold
