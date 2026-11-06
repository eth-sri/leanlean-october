module
public import MathCollab.Density.ZeroLargeValues
public import MathCollab.Density.MollifierCoefficients

@[expose] public section

open Filter
open scoped Topology

set_option autoImplicit false

noncomputable section
namespace MathCollab.Density

/-- The first density target's cutoff, distinct from other detector choices. -/
def firstDetectorX (T : ℝ) : ℝ := 2*T^(1/8 : ℝ)

def firstDetectorY (T : ℝ) : ℝ := T

/-- Scalar part of the detector error. This does not assert the analytic error bound. -/
theorem first_detector_error_scale {T β η₀ : ℝ} (hT : 1 ≤ T) (hβ : 3/4 ≤ β) :
    Real.sqrt (firstDetectorX T)*(firstDetectorY T)^(1/2-β)*T^(1/6+η₀) ≤
      Real.sqrt 2*T^(-1/48+η₀) := by
  have hTpos : 0 < T := by linarith
  have hsqrt : Real.sqrt (firstDetectorX T) = Real.sqrt 2*T^(1/16 : ℝ) := by
    rw [firstDetectorX, Real.sqrt_mul (by norm_num), Real.sqrt_eq_rpow (T^(1/8 : ℝ)),
      ← Real.rpow_mul hTpos.le]
    norm_num
  rw [hsqrt, firstDetectorY]
  have hpow : T^(1/2-β) ≤ T^(-1/4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  calc
    _ ≤ (Real.sqrt 2*T^(1/16 : ℝ))*T^(-1/4 : ℝ)*T^(1/6+η₀) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity))
        (by positivity)
    _ = _ := by
      rw [mul_assoc (Real.sqrt 2), ← Real.rpow_add hTpos, mul_assoc (Real.sqrt 2),
        ← Real.rpow_add hTpos]
      congr 2
      ring

theorem first_detector_majorant_tendsto_zero {η₀ : ℝ} (hη₀ : η₀ < 1/48) :
    Tendsto (fun T : ℝ => Real.sqrt 2*T^(-1/48+η₀)) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show 0 < 1/48-η₀ by linarith)).const_mul (Real.sqrt 2)
  have he : -(1/48-η₀) = -1/48+η₀ := by ring
  simpa only [he, mul_zero] using h

end MathCollab.Density
