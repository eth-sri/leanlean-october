module
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import DensityEnergyGM.DFIEquation12

@[expose] public section

open Set Filter Function MeasureTheory
open scoped BigOperators ContDiff FourierTransform Interval Topology

namespace GuthMaynard.NativeMoment

/-!
# DFI equations (13)--(20): quantitative delta estimates

This module derives the scale-sensitive estimates following the exact delta
identity.  Constants are kept explicit and are never represented by an
assumed big-O proposition.
-/

/-- Restricting the domain can only decrease the integral of a nonnegative
integrable real function. -/
theorem setIntegral_le_integral_of_nonneg
    (g : ℝ → ℝ) (hg : Integrable g) (hgnonneg : ∀ x, 0 ≤ g x)
    (s : Set ℝ) :
    (∫ x in s, g x) ≤ ∫ x : ℝ, g x := by
  exact MeasureTheory.integral_mono_measure Measure.restrict_le_self
    (Filter.Eventually.of_forall hgnonneg) hg

end GuthMaynard.NativeMoment
