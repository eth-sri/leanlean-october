module
public import GuthMaynard.NativeSource.GuthMaynard.TerminalTypeI
public import GuthMaynard.NativeSource.GuthMaynard.ClassicalPowering
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import GuthMaynard.NativeSource.GuthMaynard.LargeValuesReflection
public import GuthMaynard.NativeSource.GuthMaynard.DFIDivisorEpsilon

@[expose] public section

open Complex Finset MeasureTheory Real Set Filter Asymptotics Topology
open scoped BigOperators ContDiff FourierTransform SchwartzMap

namespace GuthMaynard.NativeMoment

/-!
# Finite branch-to-slab assembly for the classical density endpoints

This file contains the final consumer of the finite classical detector
dichotomy.  The preliminary lemmas below make the power selection and the
sub-polynomial losses explicit; they are used by the Type-I and Type-II
witness consumers later in the file.
-/

/-! ## The nonstationary zero Poisson mode -/









/-! ## A fixed logarithmic kernel for interior Type-I blocks -/












/-! ## Exact algebra of the reflected finite polynomial -/



/-! ## Source-facing Poisson entry -/






/-! ## Finite negative-mode extraction for the medium Type-I branch -/









/-! ## Normalized reflected blocks

The medium Type-I consumer needs the output of the exact Mellin reflection
in the coefficient-uniform form required by Montgomery--Halász--Huxley.
The cutoff at `M` is part of the coefficient, so extending the prefix to the
next dyadic endpoint introduces no mathematical remainder. -/







/-! ## Quantitative nonstationary control -/






































































/-- Any fixed natural power of `log T` is eventually dominated by an
arbitrarily small positive power of `T`. -/
theorem eventually_log_nat_power_le_rpow
    (B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, (Real.log T) ^ B ≤ T ^ η := by
  have hLittle := isLittleO_log_rpow_rpow_atTop (B : ℝ) hη
  filter_upwards [hLittle.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with T hBound hT
  have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  have hTNonneg : 0 ≤ T := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLogNonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hTNonneg _)] at hBound
  rw [← Real.rpow_natCast]
  exact hBound





/-! ## Exact Type-I basic-window witness consumer -/


set_option maxHeartbeats 800000



/-! ## Exact Type-II dichotomy-witness consumer -/

set_option maxHeartbeats 800000


end GuthMaynard.NativeMoment
