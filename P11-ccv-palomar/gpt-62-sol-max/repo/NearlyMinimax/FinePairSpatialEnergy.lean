module

public import NearlyMinimax.FinePairActionEnvelopes
public import NearlyMinimax.FineFieldSumEnergy

@[expose] public section

/-! Genuine spatial energy of the higher even-field action. All moment
bounds here concern the actual time-integrated hyperplane field law. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

 theorem finite_sum_abs_square_integrable {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ)
    (hm : ∀ i ∈ s, Measurable (f i))
    (hi : ∀ i ∈ s, Integrable (fun x => f i x ^ 2) μ) :
    Integrable (fun x => (∑ i ∈ s, |f i x|)^2) μ :=
  finite_sum_square_integrable μ s (fun i x => |f i x|) (fun i hi => (hm i hi).abs)
    (fun i h => by simpa only [sq_abs] using hi i h)

 def finePairEvenActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (finePairActionCap d n M q ad bd C a ρ η)^2 *
      fineFieldSubsetEnergyBase d ^ n * (n : ℝ)^8 * (T0 ^ (2-(d : ℝ)))^2

end NearlyMinimax
