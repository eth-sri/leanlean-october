module

public import NearlyMinimax.HistoryReferenceMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure


@[expose] public section

/-!
# Integrating genuine conditional fiber bounds over the countable history reference
-/

noncomputable section
open MeasureTheory Filter
namespace NearlyMinimax

variable {J : Type*} [Fintype J] [LinearOrder J]

/-- A uniform conditional fiber bound passes to the actual normalized countable reference law. -/
theorem historyMarkedReference_integral_le_of_fiber_bound {dependent : J → J → Prop} {Δ : ℕ}
    (geom : HistoryDegreeBound dependent Δ) (hΔ : 1 ≤ Δ)
    {E : Type*} [MeasurableSpace E] (π : Measure E) [IsProbabilityMeasure π]
    (F : HistoryMarked dependent E → ℝ) (hF : Measurable F)
    (R C : ℝ) (hbound : ∀ h, |F h| ≤ R)
    (hconditional : ∀ g, (∫ marks, F ⟨g, marks⟩
      ∂Measure.pi (fun _ : Fin (historyShapeLength dependent g) => π)) ≤ C) :
    (∫ h, F h ∂historyMarkedReference dependent Δ π) ≤ C := by
  let μ := historyMarkedReferenceRaw dependent Δ π
  let : IsFiniteMeasure μ := historyMarkedReferenceRaw_finite geom hΔ π
  let : IsProbabilityMeasure (historyMarkedReference dependent Δ π) :=
    historyMarkedReference_probability geom hΔ π
  have hi : Integrable F μ := Integrable.of_bound hF.aestronglyMeasurable R
    (Eventually.of_forall fun h => by tauto)
  have hc : Integrable (fun _ : HistoryMarked dependent E => C) μ := integrable_const C
  have hr : (∫ h, F h ∂μ) ≤ ∫ _ : HistoryMarked dependent E, C ∂μ := by
    change (∫ h, F h ∂Measure.sum _) ≤ ∫ _ : HistoryMarked dependent E, C ∂Measure.sum _
    rw [integral_sum_measure hi, integral_sum_measure hc]
    apply Summable.tsum_le_tsum (fun g => ?_)
      (hasSum_integral_measure hi).summable (hasSum_integral_measure hc).summable
    rw [integral_smul_measure, integral_smul_measure,
      integral_map (historyMarked_measurable_mk dependent g).aemeasurable hF.aestronglyMeasurable,
      integral_map (historyMarked_measurable_mk dependent g).aemeasurable measurable_const.aestronglyMeasurable]
    simp only [smul_eq_mul]
    simpa using mul_le_mul_of_nonneg_left (hconditional g) (ENNReal.toReal_nonneg)
  have he : (∫ h, F h ∂historyMarkedReference dependent Δ π) ≤
      ∫ _ : HistoryMarked dependent E, C ∂historyMarkedReference dependent Δ π := by
    unfold historyMarkedReference
    rw [integral_smul_measure, integral_smul_measure]
    gcongr
  simpa using he

end NearlyMinimax
