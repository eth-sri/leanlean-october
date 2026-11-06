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
attribute [local instance] Classical.propDecidable

 theorem finite_sum_abs_square_integrable {X I : Type*} [MeasurableSpace X]
    (μ : Measure X) (s : Finset I) (f : I → X → ℝ)
    (hm : ∀ i ∈ s, Measurable (f i))
    (hi : ∀ i ∈ s, Integrable (fun x => f i x ^ 2) μ) :
    Integrable (fun x => (∑ i ∈ s, |f i x|)^2) μ := by
  have hupper : Integrable (fun x => (s.card : ℝ) * ∑ i ∈ s, f i x ^ 2) μ :=
    (integrable_finsetSum s hi).const_mul _
  apply hupper.mono' ((Finset.measurable_sum s (fun i hi => (hm i hi).abs)).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_eq_abs, abs_sq]
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] using
      Finset.sum_mul_sq_le_sq_mul_sq s (fun _ : I => (1 : ℝ)) (fun i => |f i x|))

 def finePairEvenActionSpatialBudget (d n M q : ℕ) (ad bd C a ρ η T0 : ℝ) : ℝ :=
  (finePairDensityCoefficientBudget ad bd M n *
    (finePairResponseActionBudget d q C a ρ * (n : ℝ)^2 * η^2))^2 *
      fineFieldSubsetEnergyBase d ^ n * (n : ℝ)^8 * (T0 ^ (2-(d : ℝ)))^2

end NearlyMinimax
