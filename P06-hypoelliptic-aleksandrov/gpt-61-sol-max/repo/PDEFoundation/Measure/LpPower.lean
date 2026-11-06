module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Finite-exponent `L^p` power identities

This file relates Mathlib's extended-real `eLpNorm` to the usual real
integral-power expression when the exponent is a positive real number and the
function belongs to `L^p`.

The statements are measure-generic so that both restricted volume and
normalized restricted volume can reuse them without duplicating coercion
bookkeeping.
-/

 public section



namespace PDE

open MeasureTheory

variable {α E : Type*}

/-- For a positive finite real exponent, the real value of `eLpNorm` is the
usual integral-power expression. -/
theorem toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv
     [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {p : ℝ} (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal =
      (∫ x, ‖f x‖ ^ p ∂μ) ^ (1 / p : ℝ) := by


  rw [hf.eLpNorm_eq_integral_rpow_norm (by
      intro hzero
      exact (not_le_of_gt hp) (ENNReal.ofReal_eq_zero.mp hzero)) ENNReal.ofReal_ne_top]

  rw [ENNReal.toReal_ofReal (by
      positivity), (ENNReal.toReal_ofReal hp.le)]
  simp only [one_div]

/-- Raising the real `L^p` norm to the exponent recovers the integral of the
`p`th power. -/
theorem toReal_eLpNorm_ofReal_rpow_eq_integral_rpow_norm
     [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} {p : ℝ} (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal ^ p =
      ∫ x, ‖f x‖ ^ p ∂μ := by
  rw [toReal_eLpNorm_ofReal_eq_integral_rpow_norm_rpow_inv hp hf]
  have hintegralNonneg :
      0 ≤ ∫ x, ‖f x‖ ^ p ∂μ :=
    integral_nonneg_of_ae <|
      Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (norm_nonneg _) _
  rw [← Real.rpow_mul hintegralNonneg]

  rw [show (1 / p : ℝ) * p = 1 by field_simp [hp.ne']]
  simp only [Real.rpow_one]

end PDE
