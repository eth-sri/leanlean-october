module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import TaoTrudgianYang2025.ExponentPairBProcess
public import GenericRestrictedPeakTail

@[expose] public section
set_option autoImplicit false
noncomputable section
open Filter Finset MathCollab.Density MathCollab.Density.Stronger MathCollab.Density.Stronger.Peaks
namespace TaoTrudgianYang2025

theorem exponentPair_BHB10 : ExponentPair (64/135) (122/243) := by
  convert (exponentPair_heathBrown (by norm_num : 3 ≤ (10:ℕ))).bProcess using 1 <;> norm_num

theorem exponentPair_BHB9 : ExponentPair (371/792) (177/352) := by
  convert (exponentPair_heathBrown (by norm_num : 3 ≤ (9:ℕ))).bProcess using 1 <;> norm_num

theorem exponentPair_BHB8 : ExponentPair (129/280) (247/490) := by
  convert (exponentPair_heathBrown (by norm_num : 3 ≤ (8:ℕ))).bProcess using 1 <;> norm_num

theorem exponentPair_BHB7 : ExponentPair (85/189) (41/81) := by
  convert (exponentPair_heathBrown (by norm_num : 3 ≤ (7:ℕ))).bProcess using 1 <;> norm_num

theorem exponentPair_BHB6 : ExponentPair (13/30) (51/100) := by
  convert (exponentPair_heathBrown (by norm_num : 3 ≤ (6:ℕ))).bProcess using 1 <;> norm_num

