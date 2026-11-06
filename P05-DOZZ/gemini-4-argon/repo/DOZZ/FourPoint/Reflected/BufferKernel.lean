/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.ReflectedOuter.KernelPerturbation
import Mathlib.Tactic
/-! The moving kernel on the spatial buffer is bounded by the zero-root kernel. -/
@[expose] public section
open MeasureTheory Set
open scoped ENNReal
namespace DOZZ.Proofs


/-- The actual buffer mass is bounded by a fixed multiple of the zero-root mass in the
whole deleted disk, allowing direct reuse of the rooted freezing estimate. -/
theorem reflected_buffer_mass_upper (γ α₁ α₂ α₃ R r : ℝ) (hR : 0 ≤ R)
    z (μ : Measure ℂ) U (hU : MeasurableSet U)
    (hball : U ⊆ Metric.ball 0 r)
    (hsep : ∀ x ∈ U, 0 < ‖x‖ ∧ ‖z‖ ≤ R*‖x‖) :
    (∫⁻ x in U, ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x) ∂μ) ≤
      ENNReal.ofReal ((1+R)^(γ^2/2))*
        ∫⁻ x in Metric.ball (0 : ℂ) r,
          ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂μ := by
  have reflected_buffer_kernel_upper x (hx : 0 < ‖x‖) (hz : ‖z‖ ≤ R*‖x‖) : gammaHalfKernel γ α₁ α₂ α₃ z x ≤ (1+R)^(γ^2/2)*gammaHalfKernel γ α₁ α₂ α₃ 0 x := by
    rw [reflected_kernel_distance_ratio γ α₁ α₂ α₃ z x hx]
    apply mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (div_nonneg (norm_nonneg _) hx.le) (show ‖x-z‖/‖x‖ ≤ 1+R by apply (div_le_iff₀ hx).mpr; linarith only [(norm_sub_le x z),hz]) (by positivity : 0 ≤ γ^2/2))
    unfold gammaHalfKernel normPlus
    positivity
  calc
    _ ≤ ∫⁻ x in U, ENNReal.ofReal ((1+R)^(γ^2/2))*
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂μ := by
      apply setLIntegral_mono' hU
      intro x hx
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith only [hR]) _)]
      exact ENNReal.ofReal_le_ofReal
        (reflected_buffer_kernel_upper x (hsep x hx).1 (hsep x hx).2)
    _ ≤ ∫⁻ x in Metric.ball (0 : ℂ) r, ENNReal.ofReal ((1+R)^(γ^2/2))*
        ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ 0 x) ∂μ :=
      lintegral_mono' (Measure.restrict_mono hball le_rfl) (fun _ => le_rfl)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end DOZZ.Proofs
