module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! # Pairing bounded exit data with the actual complex L1 density -/

@[expose] public section
noncomputable section
namespace HypoellipticAleksandrov.KineticAleksandrov.LocalA
open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

/- The bounded-data/L1 pairing, using the real scalar action on complex densities. -/
def spatialDensityPairing {Z : Type} [MeasurableSpace Z] (μ : Measure Z) :
    Lp ℝ ∞ μ →L[ℝ] Lp ℂ 1 μ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).lpPairing μ ∞ 1

/- The pairing equals its ordinary Bochner integral. -/
theorem spatialDensityPairing_apply {Z : Type} [MeasurableSpace Z]
    (μ : Measure Z) (f : Lp ℝ ∞ μ) (g : Lp ℂ 1 μ) :
    spatialDensityPairing μ f g = ∫ z, f z • g z ∂μ :=  (ContinuousLinearMap.lsmul ℝ ℝ (E := ℂ)).lpPairing_eq_integral f g

/- Pairing the two data classes obeys the sharp Holder norm estimate. -/
theorem spatialData_toLp_norm_le {Z : Type} [TopologicalSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] (μ : Measure Z) [IsFiniteMeasure μ] (f : Z →ᵇ ℝ) :
    ‖BoundedContinuousFunction.toLp ∞ μ ℝ f‖ ≤ ‖f‖ := by
  have h := BoundedContinuousFunction.toLp_norm_le (E := ℝ) (p := ∞) (𝕜 := ℝ) μ
  simp only [ENNReal.toReal_top, inv_zero, Real.rpow_zero] at h
  exact (ContinuousLinearMap.le_opNorm _ f).trans
    ((mul_le_mul_of_nonneg_right h (norm_nonneg f)).trans_eq (one_mul _))

end HypoellipticAleksandrov.KineticAleksandrov.LocalA
