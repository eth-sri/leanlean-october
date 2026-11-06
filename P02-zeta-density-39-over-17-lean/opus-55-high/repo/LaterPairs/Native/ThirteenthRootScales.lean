module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosPhysicalShift
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                             

noncomputable section
namespace TaoTrudgianYang2025

section
variable {lam : ℝ} (hlam : 0 < lam)
include lam hlam
theorem thirteenth_root_nat_pow (n : ℕ) :
    (lam^(-(1:ℝ)/13))^n = lam^(-(n:ℝ)/13) := by
  rw [← Real.rpow_mul_natCast hlam.le]
  congr 1
  ring

theorem thirteenth_root_physical_scale (hsmall : lam ≤ 1/8192) :
    2 ≤ lam^(-(1:ℝ)/13) ∧ (lam^(-(1:ℝ)/13))^13*lam = 1 := by
  pm_773
  have hb := Real.rpow_le_rpow_of_nonpos hlam hsmall
    (show -(1:ℝ)/13 ≤ 0 by norm_num)
  pm_1248
  refine ⟨by grind,?_⟩
  rw [thirteenth_root_nat_pow hlam]
  norm_num
  rw [Real.rpow_neg_one,inv_mul_cancel₀ hlam.ne']
end

theorem positive_floor_half_bounds {X : ℝ} (hX : 1 ≤ X) :
    0 < ⌊X⌋₊ ∧ X/2 ≤ (⌊X⌋₊:ℝ) ∧ (⌊X⌋₊:ℝ) ≤ X := by
  pm_8613 hp X hX
  pm_6109 h1 X hp
  have hn := Nat.lt_floor_add_one X
  exact ⟨hp,by linarith,Nat.floor_le (by linarith)⟩

end TaoTrudgianYang2025
