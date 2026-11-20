module
/-
Copyright (c) 2026 S. McColm. All rights reserved.
Released under MIT-0; see repository-root third_party/twelfth/LICENSE-MIT-0.
Adapted from source pin 6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1.
Mathlib and the existing contour/Digamma sources retain Apache-2.0 attribution.
No upstream project or Architect module is imported.
-/
public import MathCollab.Density.Stronger.Atkinson.ShortDivisorSource

@[expose] public section

open Complex Filter MeasureTheory Set Topology
open MathCollab.Density.Stronger MathCollab.Density.Stronger.Fourth
open MathCollab.Density.Contour
open scoped Interval ComplexConjugate ContDiff
set_option autoImplicit false
noncomputable section
namespace MathCollab.Density.Stronger.Atkinson

theorem exp_sub_one_le_two_mul {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x - 1 ≤ 2 * x := by
  have h := Real.norm_exp_sub_one_sub_id_le (x := x)
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hx] using hx1)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hx] at h
  have hle := (le_abs_self (Real.exp x - 1 - x)).trans h
  nlinarith

def zetaShortDivisorTestFunction (T G x : ℝ) : ℂ :=
  (x : ℂ) ^ ((-1 / 2 : ℂ) + (T : ℂ) * I) *
    zetaDivisorWeight ((Real.log x : ℂ) - zetaGammaLeadingLog T) *
    zetaSquareReflectedGammaPhase T *
    zetaGaussianQuadraticIntegral T G (Real.log x - Real.log (T / (2 * Real.pi)))

theorem zetaQuadraticDivisorTerm_eq_testFunction (T G : ℝ) (n : ℕ) :
    zetaFrozenDivisorCoefficient T n * zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G (Real.log (n : ℝ) - Real.log (T / (2 * Real.pi))) =
      divisorWeight n * zetaShortDivisorTestFunction T G n := by
  have hs : -afeCriticalPoint (-T) = (-1 / 2 : ℂ) + (T : ℂ) * I := by
    unfold afeCriticalPoint
    push_cast
    ring
  simp only [zetaFrozenDivisorCoefficient, divisorDirichletTerm_eq_divisorWeight_mul_cpow,
    hs, zetaShortDivisorTestFunction, zetaDivisorWeightArgument, Complex.ofReal_natCast]
  ring

end MathCollab.Density.Stronger.Atkinson
