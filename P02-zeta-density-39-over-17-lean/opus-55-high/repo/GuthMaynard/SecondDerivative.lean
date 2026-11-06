module
public import GuthMaynard.VanDerCorput
public import GuthMaynard.NativeSource.GuthMaynard.SecondDerivative

@[expose] public section

open Complex Finset Set

namespace RiemannZeta.GuthMaynard

/-!
# Multi-period van der Corput second-derivative estimate

This module partitions a monotone sequence of phase increments into full
`2 * pi` periods.  Kusmin--Landau controls the interior of every period;
the lower second-difference bound counts the two short endpoint pieces.
-/

export GuthMaynard.NativeMoment (vanDerCorput_second_derivative kusminLandau_good_fiber filter_card_bound period_count_bound vanDerCorput_B_process discrete_growth_lower discrete_growth_upper sum_Icc_eq_shifted_range periodIndex_bounds monotone_of_step norm_phase_sum_finset_le_card periodIndex_mono periodIndex)

end RiemannZeta.GuthMaynard
