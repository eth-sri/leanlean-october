module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.FresnelGaussianComparison
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Abel limit and quantitative Fresnel truncation

The zero-damping limit is taken on each finite interval. A damping-uniform
oscillatory tail identifies the limiting Gaussian value; no whole-line
Lebesgue integral at zero damping is asserted.
-/

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Topology

namespace MathCollab.Density.Stronger.Atkinson

/-- The literal finite quadratic window, extracted from AtkinsonFiniteStationaryMain. -/
def atkinsonQuadraticWindow (c H : ℝ) : ℂ :=
  ∫ z in (-H)..H, Complex.exp (((-2 * Real.pi * c * z ^ 2 : ℝ) : ℂ) * I)


def fresnelGaussianValue (c : ℝ) : ℂ :=
  ((Real.pi : ℂ) / (2 * Real.pi * c * I)) ^ (1 / 2 : ℂ)

section
variable {c : ℝ} (hc : 0 < c)
include c hc
theorem fresnelGaussianBase :
    (Real.pi : ℂ) / (2 * Real.pi * c * I) = -I / ((2 * c : ℝ) : ℂ) := by
  pm_115 hcC c Complex.ofReal_ne_zero.mpr hc.ne'
  pm_115 hpiC Real.pi Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp
  simp_all

theorem continuousAt_fresnelGaussianValue_damping :
    ContinuousAt (fun ε : ℝ =>
      ((Real.pi : ℂ) / ((ε : ℂ) + 2 * Real.pi * c * I)) ^ (1 / 2 : ℂ)) 0 := by
  pm_115 hcC c Complex.ofReal_ne_zero.mpr hc.ne'
  pm_115 hpiC Real.pi Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hden : ((0 : ℝ) : ℂ) + 2 * Real.pi * c * I ≠ 0 := by
    simp_all
  have hbase : (Real.pi : ℂ) / (2 * Real.pi * c * I) ∈ slitPlane := by
    rw [fresnelGaussianBase hc]
    apply Or.inr
    rw [Complex.div_ofReal_im, Complex.neg_im, Complex.I_im]
    grind
  have hquot : ContinuousAt (fun ε : ℝ => (Real.pi : ℂ) /
      ((ε : ℂ) + 2 * Real.pi * c * I)) 0 :=
    continuousAt_const.div (Complex.continuous_ofReal.continuousAt.add continuousAt_const) hden
  have hbase' : (Real.pi : ℂ) / (((0 : ℝ) : ℂ) + 2 * Real.pi * c * I) ∈ slitPlane := by
    simp_all
  fun_prop
end

theorem fresnelDampedKernel_zero (c x : ℝ) :
    fresnelDampedKernel 0 c x = Complex.exp (((-2 * Real.pi * c * x ^ 2 : ℝ) : ℂ) * I) := by
  unfold fresnelDampedKernel
  congr 1
  push_cast
  ring

theorem continuous_fresnelDampedWindow (c H : ℝ) :
    Continuous (fun ε : ℝ => ∫ x in (-H)..H, fresnelDampedKernel ε c x) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  unfold Function.uncurry fresnelDampedKernel
  fun_prop

theorem norm_atkinsonQuadraticWindow_sub_gaussianValue_le {c H : ℝ}
    (hc : 0 < c) (hH : 0 < H) :
    ‖atkinsonQuadraticWindow c H - fresnelGaussianValue c‖ ≤ 2 / (c * H * Real.pi) := by
  have hG : Tendsto (fun ε : ℝ =>
      ((Real.pi : ℂ) / ((ε : ℂ) + 2 * Real.pi * c * I)) ^ (1 / 2 : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 (fresnelGaussianValue c)) := by
    simpa only [Complex.ofReal_zero, zero_add, fresnelGaussianValue] using
      (continuousAt_fresnelGaussianValue_damping hc).tendsto.mono_left nhdsWithin_le_nhds
  have hW : Tendsto (fun ε : ℝ => ∫ x in (-H)..H, fresnelDampedKernel ε c x)
      (𝓝[>] (0 : ℝ)) (𝓝 (atkinsonQuadraticWindow c H)) := by
    have h := (continuous_fresnelDampedWindow c H).continuousAt
      (x := (0 : ℝ)) |>.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa only [fresnelDampedKernel_zero, atkinsonQuadraticWindow] using h
  rw [norm_sub_rev]
  apply le_of_tendsto (hG.sub hW).norm
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact norm_gaussianValue_sub_fresnelDampedWindow_le hε hc hH

end MathCollab.Density.Stronger.Atkinson
