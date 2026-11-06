module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.IntervalAmplitudeBounds
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuous kernels with a bounded primitive

Integration by parts consumes the actual C1 amplitude and the literal
primitive integral. The Fresnel application constructs the primitive bound.
-/

noncomputable section

open Complex MeasureTheory Set

namespace MathCollab.Density.Stronger.Atkinson

theorem IntervalC1Bound.continuousKernel_of_primitive_bound {f K : ℝ → ℂ}
    {a c M B : ℝ} (hf : IntervalC1Bound f a c M)
    (hK : Continuous K) (hac : a ≤ c)
    (hprimitive : ∀ x ∈ Icc a c, ‖∫ y in a..x, K y‖ ≤ B) :
    ‖∫ y in a..c, f y * K y‖ ≤ 2 * B * M := by
  pm_5547 hB B hprimitive hac
  pm_8469 F K
  have hd (x : ℝ) : HasDerivAt F (K x) x :=
    intervalIntegral.integral_hasDerivAt_right (hK.intervalIntegrable a x)
      hK.stronglyMeasurable.stronglyMeasurableAtFilter hK.continuousAt
  have hF : Continuous F := continuous_iff_continuousAt.mpr fun x => (hd x).continuousAt
  pm_963 hFb c F
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := f) (u' := deriv f) (v := F) (v' := K)
    (fun x hx => by
      rw [uIcc_of_le hac] at hx
      exact ((hf.smooth x hx).differentiableAt (by norm_num)).hasDerivAt)
    (fun x _ => hd x) (hf.derivative_integrable hac) (hK.intervalIntegrable a c)
  pm_83 hF.norm.continuousOn

end MathCollab.Density.Stronger.Atkinson
