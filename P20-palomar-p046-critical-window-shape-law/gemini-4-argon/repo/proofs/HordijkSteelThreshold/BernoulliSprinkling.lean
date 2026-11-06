module

public import proofs.HordijkSteelThreshold.AmbientIndependence

@[expose] public section

namespace HordijkSteelThreshold
open Classical MeasureTheory ProbabilityTheory unitInterval

@[simp] theorem ambientCoordLaw_false (p : I) :
    ambientCoordLaw p {False} = toNNReal (σ p) := by
  simp [ambientCoordLaw]

theorem probability_prop_eq_of_false (μ ν : Measure Prop)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (h : μ {False} = ν {False}) : μ = ν := by
  apply Measure.ext_of_singleton; intro q
  by_cases hq : q
  · rw [propext (iff_true_intro hq), show ({True} : Set Prop) = {False}ᶜ by ext; simp,
      measure_compl (.singleton _) (measure_ne_top _ _),
      measure_compl (.singleton _) (measure_ne_top _ _), measure_univ, measure_univ, h]
  · simpa only [propext (iff_false_intro hq)] using h

def sprinklingParameter (a b : I) : I := σ ((σ a) * (σ b))

theorem sprinklingParameter_value (a b : I) :
    (sprinklingParameter a b : ℝ) = (a : ℝ) + (1-(a : ℝ))*(b : ℝ) := by
  change 1-((1-(a : ℝ))*(1-(b : ℝ))) = _
  ring

theorem ambientCoordLaw_union (a b : I) :
    ((ambientCoordLaw a).prod (ambientCoordLaw b)).map (fun p : Prop × Prop => p.1 ∨ p.2) =
      ambientCoordLaw (sprinklingParameter a b) := by
  apply probability_prop_eq_of_false
  rw [Measure.map_apply (measurable_of_finite _) (.singleton False),
    show (fun p : Prop × Prop => p.1 ∨ p.2) ⁻¹' {False} = ({False} : Set Prop) ×ˢ {False} by
      ext; simp [Prod.ext_iff], Measure.prod_prod]
  simp [ambientCoordLaw, sprinklingParameter, ← ENNReal.coe_mul]
  rfl

end HordijkSteelThreshold
