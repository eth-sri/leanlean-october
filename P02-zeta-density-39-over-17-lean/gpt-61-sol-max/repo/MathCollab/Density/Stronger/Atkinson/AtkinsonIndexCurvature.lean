module
import Mathlib
/-
Selected proof adapted from Scott McColm's Lean repository, revision
6e2d10c6c2252ee1575bb7ef12dea12e2f1a3af1, MIT-0.
Copyright 2026 S. McColm.
See ../../../../../third_party/twelfth/ATKINSON_PREFIX_MANIFEST.json
and ../../../../../third_party/twelfth/LICENSE-MIT-0.
-/
public import MathCollab.Density.Stronger.Atkinson.AtkinsonIndexPhase

@[expose] public section

/-!
Adapted from the inspected adjacent `GafniTao.HeathBrownAtkinsonRealCurvature` proof.
This local version uses the current native foundation and the exact
`atkinsonSourcePhase`; it imports no adjacent moment theorem.

# Curvature of the real-index Atkinson phase

This file proves the exact second derivative in the summation variable and
the corresponding identity for a difference of two source phases.  These
are the differential identities immediately preceding the exponent-pair
estimate in Heath--Brown's argument.
-/

namespace MathCollab.Density.Stronger.Atkinson

noncomputable section

/-- The exact real-index slope of the Atkinson phase. -/
def atkinsonIndexRealSlope (T x : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * T / x + Real.pi ^ (2 : ℕ))

/-- The exact real-index curvature of the Atkinson phase. -/
def atkinsonIndexRealCurvature (T x : ℝ) : ℝ :=
  -(Real.pi * T) /
    (x ^ (2 : ℕ) * atkinsonIndexRealSlope T x)

section
variable {T x : ℝ} (hT : 0 < T) (hx : 0 < x)
include T x hT hx

theorem atkinsonIndexRealSlope_pos
     :
    0 < atkinsonIndexRealSlope T x := by
  unfold atkinsonIndexRealSlope
  apply Real.sqrt_pos.2
  positivity

/-- Exact derivative of the phase slope, hence the second derivative of
the equation-(11) phase. -/
theorem hasDerivAt_atkinsonIndexRealSlope
     :
    HasDerivAt (atkinsonIndexRealSlope T)
      (atkinsonIndexRealCurvature T x) x := by
  have hdiv : HasDerivAt (fun u : ℝ => 2 * Real.pi * T / u)
      (-(2 * Real.pi * T) / x ^ (2 : ℕ)) x := by
    simpa using! (hasDerivAt_const x (2 * Real.pi * T)).div
      (hasDerivAt_id x) hx.ne'
  have hradicand : HasDerivAt
      (fun u : ℝ => 2 * Real.pi * T / u + Real.pi ^ (2 : ℕ))
      (-(2 * Real.pi * T) / x ^ (2 : ℕ)) x := by simp_all
  have hpos : 0 < 2 * Real.pi * T / x + Real.pi ^ (2 : ℕ) := by
    positivity
  have hsqrt := hradicand.sqrt hpos.ne'
  unfold atkinsonIndexRealSlope atkinsonIndexRealCurvature
  convert hsqrt using 1
  simp only [atkinsonIndexRealSlope]
  ring
end


/-- Difference of two exact Atkinson phases, with the later height first. -/
def atkinsonIndexPhaseDifference (t u x : ℝ) : ℝ :=
  atkinsonIndexRealPhase t x - atkinsonIndexRealPhase u x

/-- Exact first derivative of the phase difference. -/
theorem hasDerivAt_atkinsonIndexPhaseDifference
    {t u x : ℝ} (ht : 0 < t) (hu : 0 < u) (hx : 0 < x) :
    HasDerivAt (atkinsonIndexPhaseDifference t u)
      (atkinsonIndexRealSlope t x -
        atkinsonIndexRealSlope u x) x := by
  unfold atkinsonIndexPhaseDifference atkinsonIndexRealSlope
  exact (hasDerivAt_atkinsonIndexRealPhase ht hx).sub
    (hasDerivAt_atkinsonIndexRealPhase hu hx)




