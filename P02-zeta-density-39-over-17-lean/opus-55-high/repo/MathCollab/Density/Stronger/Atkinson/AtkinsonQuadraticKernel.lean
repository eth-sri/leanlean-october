module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSaddleTaylor
public import MathCollab.Density.Stronger.Atkinson.AtkinsonSaddleNormalization
public import MathCollab.Density.Stronger.Atkinson.FresnelEvaluation
import WeylPort.Analytic.RealLaplace

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-! # Actual quadratic saddle kernel and its finite-window identity

The exact signed carrier and curvature are retained. This module evaluates
its quadratic approximation, without asserting an amplitude/source reduction.
-/
noncomputable section
open Complex MeasureTheory Set
namespace MathCollab.Density.Stronger.Atkinson

def atkinsonRootQuadraticKernel (T b y : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * atkinsonRootQuadratic T b y : ℝ) : ℂ) * I)

theorem norm_atkinsonRootQuadraticKernel (T b y : ℝ) :
    ‖atkinsonRootQuadraticKernel T b y‖ = 1 := by
  simp [atkinsonRootQuadraticKernel, Complex.norm_exp]

theorem continuous_atkinsonRootQuadraticKernel (T b : ℝ) :
    Continuous (atkinsonRootQuadraticKernel T b) := by
  unfold atkinsonRootQuadraticKernel atkinsonRootQuadratic
  fun_prop

def atkinsonSaddleCurvature (T b : ℝ) : ℝ :=
  1 + (T / (2 * Real.pi)) / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2

section
variable {T : ℝ} (hT : 0 < T) (b : ℝ)
include T hT b
theorem one_lt_atkinsonSaddleCurvature :
    1 < atkinsonSaddleCurvature T b := by
  pm_7948 hr atkinsonSaddleRoot_pos
  unfold atkinsonSaddleCurvature
  have hp : 0 < (T / (2 * Real.pi)) / (atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2 := by
    positivity
  linarith

theorem atkinsonSaddleCurvature_mul_root :
    atkinsonSaddleCurvature T b * atkinsonSaddleRoot (T / (2 * Real.pi)) b =
      Real.sqrt (b ^ 2 + 4 * (T / (2 * Real.pi))) := by
  pm_4412
  let s := atkinsonSaddleRoot (T / (2 * Real.pi)) (-b)
  pm_4370
  have hprod : r * s = T / (2 * Real.pi) := atkinsonSaddleRoot_mul_neg (by positivity) b
  have hsum : r + s = Real.sqrt (b ^ 2 + 4 * (T / (2 * Real.pi))) :=
    atkinsonSaddleRoot_sum_neg _ b
  change (1 + (T / (2 * Real.pi)) / r ^ 2) * r = _
  rw [← hsum, ← hprod]
  field_simp

theorem atkinsonSaddle_squareRoot_normalization :
    Real.sqrt (atkinsonSaddleCurvature T b) *
      Real.sqrt (atkinsonSaddleRoot (T / (2 * Real.pi)) b) =
        Real.sqrt (Real.sqrt (b ^ 2 + 4 * (T / (2 * Real.pi)))) := by
  rw [← Real.sqrt_mul (by linarith [one_lt_atkinsonSaddleCurvature hT b]),
    atkinsonSaddleCurvature_mul_root hT b]
end

theorem atkinsonRootQuadraticKernel_translate (T b z : ℝ) :
    atkinsonRootQuadraticKernel T b (z + atkinsonSaddleRoot (T / (2 * Real.pi)) b) =
      atkinsonRootKernel T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
        Complex.exp (((-2 * Real.pi * atkinsonSaddleCurvature T b * z ^ 2 : ℝ) : ℂ) * I) := by
  unfold atkinsonRootQuadraticKernel atkinsonRootQuadratic atkinsonRootKernel atkinsonSaddleCurvature
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integral_atkinsonRootQuadraticKernel (T b H : ℝ) :
    (∫ y in (atkinsonSaddleRoot (T / (2 * Real.pi)) b - H)..
      (atkinsonSaddleRoot (T / (2 * Real.pi)) b + H), atkinsonRootQuadraticKernel T b y) =
      atkinsonRootKernel T b (atkinsonSaddleRoot (T / (2 * Real.pi)) b) *
        atkinsonQuadraticWindow (atkinsonSaddleCurvature T b) H := by
  pm_4412
  have hs := intervalIntegral.integral_comp_add_right (atkinsonRootQuadraticKernel T b) r
    (a := -H) (b := H)
  rw [show -H + r = r - H by ring, show H + r = r + H by ring] at hs
  change (∫ y in (r - H)..(r + H), atkinsonRootQuadraticKernel T b y) = _
  rw [← hs]
  simp_rw [show ∀ z, atkinsonRootQuadraticKernel T b (z + r) =
    atkinsonRootKernel T b r *
      Complex.exp (((-2 * Real.pi * atkinsonSaddleCurvature T b * z ^ 2 : ℝ) : ℂ) * I) from
        atkinsonRootQuadraticKernel_translate T b]
  rw [intervalIntegral.integral_const_mul]
  rfl

end MathCollab.Density.Stronger.Atkinson
