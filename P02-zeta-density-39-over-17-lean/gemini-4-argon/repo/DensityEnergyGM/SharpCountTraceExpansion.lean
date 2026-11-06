module
public import DensityEnergyGM.SharpCountMonomials

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Finset
namespace Montgomery.RationalMoment

theorem fractional_constant_le_one_add {C d : ℝ}
    (hC : 0 ≤ C) (hd : 0 ≤ d) (hd1 : d ≤ 1) : C^d ≤ 1+C := by
  by_cases hC1 : 1 ≤ C
  · have h := Real.rpow_le_self_of_one_le hC1 hd1
    linarith
  · have h := Real.rpow_le_one hC (le_of_not_ge hC1) hd
    linarith


