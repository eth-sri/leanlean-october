module

public import NearlyMinimax.DerivativeRule
public import Mathlib.MeasureTheory.VectorMeasure.Integral

@[expose] public section

/-! Actual finite signed measures representing the paper's finite moment rules. -/
noncomputable section
namespace NearlyMinimax
open scoped BigOperators ENNReal
open MeasureTheory VectorMeasure Polynomial

section Atomic
variable {ι X : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- A finite atomic signed measure, retaining all weights even if atoms coincide. -/
def atomicSignedRule (z : ι → X) (w : ι → ℝ) : SignedMeasure X :=
  ∑ i, VectorMeasure.dirac (z i) (w i)

/-- The positive measure of absolute atom weights dominates the total variation. -/
def atomicVariationBound (z : ι → X) (w : ι → ℝ) : Measure X :=
  ∑ i, ‖w i‖₊ • Measure.dirac (z i)

private theorem atomic_dirac_integrable (x : X) (w : ℝ) (f : X → ℝ) :
    (VectorMeasure.dirac x w).Integrable f := by
  change Integrable f (VectorMeasure.dirac x w).variation
  rw [VectorMeasure.variation_dirac]
  change Integrable f (‖w‖₊ • Measure.dirac x)
  exact (integrable_dirac (by exact enorm_lt_top)).smul_measure_nnreal

variable (z : ι → X) (w : ι → ℝ)

/-- Integration against the actual signed measure equals the original finite-sum action. -/
theorem atomicSignedRule_integral (f : X → ℝ) :
    ∫ᵛ x, f x ∂<•(atomicSignedRule z w) = ∑ i, w i * f (z i) := by
  rw [atomicSignedRule, integral_finsetSum_vectorMeasure
    (fun i hi => atomic_dirac_integrable (z i) (w i) f)]
  simp [mul_comm]

theorem atomicSignedRule_variation_le :
    (atomicSignedRule z w).variation ≤ atomicVariationBound z w := by
  apply (VectorMeasure.variation_finsetSum_le Finset.univ _).trans_eq
  simp only [VectorMeasure.variation_dirac]
  rfl

instance atomicVariationBound_finite :
    IsFiniteMeasure (atomicVariationBound z w) := by
  unfold atomicVariationBound
  infer_instance

instance atomicSignedRule_variation_finite :
    IsFiniteMeasure (atomicSignedRule z w).variation :=
  isFiniteMeasure_of_le (atomicVariationBound z w) (atomicSignedRule_variation_le z w)

end Atomic

end NearlyMinimax
