module
public import GuthMaynard.SecondDerivative
public import GuthMaynard.NativeSource.GuthMaynard.VanDerCorput

@[expose] public section

open Complex Finset Set
open scoped BigOperators

namespace GuthMaynard.NativeMoment

-- Share the classical exponential-sum implementation.
export RiemannZeta.GuthMaynard (
  sum_Icc_eq_shifted_range
  vanDerCorput_B_process
  vanDerCorput_second_derivative
)

/-!
# Multi-period van der Corput second-derivative estimate

This module partitions a monotone sequence of phase increments into full
`2 * pi` periods.  Kusmin--Landau controls the interior of every period;
the lower second-difference bound counts the two short endpoint pieces.
-/

end GuthMaynard.NativeMoment
