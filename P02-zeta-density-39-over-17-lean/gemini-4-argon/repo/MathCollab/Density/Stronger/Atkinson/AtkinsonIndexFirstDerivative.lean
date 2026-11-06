module
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonIndexBProcess
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
Adapted from the inspected adjacent `GafniTao.HeathBrownAtkinsonFirstDerivative` proof.
This local version uses the current native foundation and the exact
`atkinsonSourcePhase`; it imports no adjacent moment theorem.

# First-derivative bounds for differences of Atkinson phases

This file supplies the first-derivative alternative used together with the
`(1/2,1/2)` B-process in Ivić (7.19).  The bounds retain literal radical
scales on a dyadic index box; no exponent-pair estimate is postulated.
-/

open Set

namespace MathCollab.Density.Stronger.Atkinson

set_option autoImplicit false
noncomputable section



/-- Rationalization of the exact square-root slope difference. -/
theorem atkinsonIndexRealSlope_sub_eq
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    atkinsonIndexRealSlope t x -
        atkinsonIndexRealSlope u x =
      (2 * Real.pi * (t - u) / x) /
        (atkinsonIndexRealSlope t x +
          atkinsonIndexRealSlope u x) := by
  have hst := atkinsonIndexRealSlope_pos ht hx
  have hsu := atkinsonIndexRealSlope_pos hu hx
  have hden : atkinsonIndexRealSlope t x +
      atkinsonIndexRealSlope u x ≠ 0 := by positivity
  have htsq : (atkinsonIndexRealSlope t x) ^ (2 : ℕ) =
      2 * Real.pi * t / x + Real.pi ^ (2 : ℕ) := by
    unfold atkinsonIndexRealSlope
    rw [Real.sq_sqrt]
    positivity
  have husq : (atkinsonIndexRealSlope u x) ^ (2 : ℕ) =
      2 * Real.pi * u / x + Real.pi ^ (2 : ℕ) := by
    unfold atkinsonIndexRealSlope
    rw [Real.sq_sqrt]
    positivity
  apply (eq_div_iff hden).2
  calc
    (atkinsonIndexRealSlope t x -
          atkinsonIndexRealSlope u x) *
        (atkinsonIndexRealSlope t x +
          atkinsonIndexRealSlope u x) =
        (atkinsonIndexRealSlope t x) ^ (2 : ℕ) -
          (atkinsonIndexRealSlope u x) ^ (2 : ℕ) := by ring
    _ = 2 * Real.pi * (t - u) / x := by rw [htsq, husq]; ring







