module

public import NearlyMinimax.DerivativeRule
public import RoughRegime.Macro
public import Mathlib.MeasureTheory.VectorMeasure.Integral

𝗎

/-! Actual finite signed measures representing the paper's finite moment rules. -/
𝚳
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
  exact (integrable_dirac enorm_lt_top).smul_measure_nnreal

/-- Integration against the actual signed measure equals the original finite-sum action. -/
theorem atomicSignedRule_integral z (w : ι → ℝ) (f : X → ℝ) :
    ∫ᵛ x, f x ∂<• atomicSignedRule z w = ∑ i, w i * f (z i) := by
  rw [atomicSignedRule, integral_finsetSum_vectorMeasure
     fun i hi => atomic_dirac_integrable (z i) (w i) f ]
  simp

theorem atomicSignedRule_variation_le (z : ι → X) w :
    (atomicSignedRule z w).variation ≤ atomicVariationBound z w := by
  apply (VectorMeasure.variation_finsetSum_le Finset.univ _).trans_eq
  aesop
