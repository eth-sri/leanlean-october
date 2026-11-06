module
/-
Copyright (c) 2026 S. McColm. Released under the MIT-0 license.
Ported from McColm 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Narrow extraction only; see third_party/twelfth/ATKINSON_STATIONARY_MANIFEST.json for source and receiver hashes.
The reused nonstationary foundation retains its Apache-2.0 attribution.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonRootIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Quantitative quadratic remainder at the actual root saddle

The cubic error is derived from the true logarithm, with no supplied
stationary-phase estimate. It controls the actual oscillatory kernel locally.
-/

noncomputable section

open Complex

namespace MathCollab.Density.Stronger.Atkinson

def atkinsonRootQuadratic (T b y : ℝ) : ℝ :=
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  atkinsonRootPhase T b r - (1 + (T / (2 * Real.pi)) / r ^ 2) * (y - r) ^ 2

theorem atkinsonRootPhase_sub_quadratic {T y : ℝ} (hT : 0 < T) (hy : 0 < y) (b : ℝ) :
    atkinsonRootPhase T b y - atkinsonRootQuadratic T b y =
      (T / Real.pi) * (Real.log (1 + (y - atkinsonSaddleRoot (T / (2 * Real.pi)) b) /
        atkinsonSaddleRoot (T / (2 * Real.pi)) b) -
          (y - atkinsonSaddleRoot (T / (2 * Real.pi)) b) /
            atkinsonSaddleRoot (T / (2 * Real.pi)) b +
              ((y - atkinsonSaddleRoot (T / (2 * Real.pi)) b) /
                atkinsonSaddleRoot (T / (2 * Real.pi)) b) ^ 2 / 2) := by
  let r := atkinsonSaddleRoot (T / (2 * Real.pi)) b
  have hr : 0 < r := atkinsonSaddleRoot_pos (by positivity) b
  have he : r ^ 2 - b * r = T / (2 * Real.pi) := atkinsonSaddleRoot_equation (by positivity) b
  have hlog : Real.log y = Real.log r + Real.log (1 + (y - r) / r) := by
    rw [show 1 + (y - r) / r = y / r by field_simp; ring,
      Real.log_div hy.ne' hr.ne']
    ring
  change atkinsonRootPhase T b y -
    (atkinsonRootPhase T b r - (1 + (T / (2 * Real.pi)) / r ^ 2) * (y - r) ^ 2) = _
  change _ = (T / Real.pi) * (Real.log (1 + (y - r) / r) - (y - r) / r + ((y - r) / r) ^ 2 / 2)
  unfold atkinsonRootPhase
  rw [hlog, show T / Real.pi = 2 * (T / (2 * Real.pi)) by ring, ← he]
  field_simp
  ring

theorem norm_exp_real_phase_sub_le (a b : ℝ) :
    ‖Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I)‖ ≤ |a - b| := by
  have he : Complex.exp ((a : ℂ) * I) - Complex.exp ((b : ℂ) * I) =
      Complex.exp ((b : ℂ) * I) * (Complex.exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  rw [he, norm_mul, show ‖Complex.exp ((b : ℂ) * I)‖ = 1 by simp [Complex.norm_exp], one_mul]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

