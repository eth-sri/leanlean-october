module

public import NearlyMinimax.PoissonCellField
public import NearlyMinimax.EvenCellPairs

@[expose] public section

/-! Exact occupancy moments of the constructed Poisson cell field. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace NearlyMinimax
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]

variable (μ : Measure H) [IsProbabilityMeasure μ] (r : ℝ≥0) {ρ : H → X → Fin 2}
    (hρ : Measurable (Function.uncurry ρ))
include hρ

theorem partitionFieldFiber_product_integrable (n j : ℕ)
    (U : Fin j → X) :
    Integrable (fun z => ∏ l, partitionFieldFiberValue ρ z (U l))
      (partitionFieldFiberLaw μ n) := by
  apply Integrable.of_bound
    (Finset.measurable_prod _ (fun l _ =>
      partitionFieldFiberValue_measurable_fixed hρ n (U l))).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall (fun z => by
    simp [Real.norm_eq_abs, Finset.abs_prod, partitionFieldFiberValue_abs,
      Finset.prod_const_one, le_refl])

theorem partitionFieldFiber_product_moment (n j : ℕ)
    (U : Fin j → X) :
    (∫ z, ∏ l, partitionFieldFiberValue ρ z (U l) ∂partitionFieldFiberLaw μ n) =
      ∫ h, if ∀ p,
        Even ((Finset.univ.filter (fun l => partitionFieldPattern ρ h (U l) = p)).card)
        then 1 else 0 ∂Measure.pi (fun _ : Fin n => μ) := by
  rw [partitionFieldFiberLaw, integral_prod _
    (partitionFieldFiber_product_integrable μ hρ n j U)]
  simp only [partitionFieldFiberValue, cellSign_product_moment]

theorem poissonCellField_product_moment_nonneg {j : ℕ}
    (U : Fin j → X) :
    0 ≤ ∫ z, ∏ l, poissonCellFieldValue ρ z (U l) ∂poissonCellFieldLaw μ r := by
  rw [poissonCellField_integral_series μ r
    (Finset.measurable_prod _ (fun l _ => poissonCellFieldValue_measurable_fixed hρ (U l)))
    (fun z => by simp [Finset.abs_prod, poissonCellFieldValue_abs,
      Finset.prod_const_one, le_refl])]
  apply tsum_nonneg
  intro n
  simp only [poissonCellFieldValue, partitionFieldFiber_product_moment μ hρ]
  positivity

end NearlyMinimax
