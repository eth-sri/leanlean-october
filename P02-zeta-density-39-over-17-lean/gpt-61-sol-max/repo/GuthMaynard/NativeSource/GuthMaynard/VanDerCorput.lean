module
public import GuthMaynard.VanDerCorput
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

open Complex Finset Set
open scoped BigOperators InnerProductSpace

namespace GuthMaynard.NativeMoment

-- Share the classical exponential-sum implementation.
export RiemannZeta.GuthMaynard (
  hasDerivAt_logarithmicPhase
  kusminLandau_interval
  logarithmicPhase
  logarithmicSum
  norm_logarithmicSum_le_length
  norm_sum_sq_le_card_mul_sum_norm_sq
  norm_unitaryPhase
  paddedShift
  phaseSum
  sum_norm_sq_paddedShift_eq
  sum_paddedShift_eq
  unitaryPhase
  unitaryPhase_logarithmicPhase_eq_cpow
  unitaryPhase_sub
)

/-!
# The logarithmic exponential sums used in the classical density argument

This file develops the two concrete van der Corput estimates needed by the
project.  Angles in `unitaryPhase` are measured in radians; this avoids a
pervasive factor `2 * pi` when the phase is `-t * log x`.
-/

theorem logarithmicSum_eq_cpow (t : ℝ) (A B : ℕ) (hA : 0 < A) :
    logarithmicSum t A B = ∑ n ∈ Ico A B, (n : ℂ) ^ (-(t : ℂ) * I) := by
  unfold logarithmicSum phaseSum
  apply Finset.sum_congr rfl
  intro n hn
  exact unitaryPhase_logarithmicPhase_eq_cpow t n (hA.trans_le (mem_Ico.mp hn).1)

/-! ## Kusmin--Landau cancellation -/

/-! ## Finite Weyl differencing -/

end GuthMaynard.NativeMoment
