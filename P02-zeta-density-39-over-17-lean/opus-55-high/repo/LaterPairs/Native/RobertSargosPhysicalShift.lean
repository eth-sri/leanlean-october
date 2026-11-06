module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.ThirdDerivativeRpowScale
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                            

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_physical_shift_scale {lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192) :
    4 ≤ lam^(-(2:ℝ)/13) := by
  pm_773
  have hb := Real.rpow_le_rpow_of_nonpos hlam hsmall
    (show -(2:ℝ)/13 ≤ 0 by norm_num)
  pm_1248
  grind

theorem robertSargos_physical_floor_shift
    (M : ℕ) {lam : ℝ} (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) :
    2 ≤ ⌊lam^(-(2:ℝ)/13)⌋₊ ∧
      ⌊lam^(-(2:ℝ)/13)⌋₊ ≤ M ∧
      lam^(-(2:ℝ)/13)/2 ≤ (⌊lam^(-(2:ℝ)/13)⌋₊:ℝ) ∧
      (⌊lam^(-(2:ℝ)/13)⌋₊:ℝ) ≤ lam^(-(2:ℝ)/13) := by
  have hR := robertSargos_physical_shift_scale hlam hsmall
  pm_6615 hRp
  have htwo : 2 ≤ ⌊lam^(-(2:ℝ)/13)⌋₊ :=
    Nat.le_floor (by grind)
  have hfloor := Nat.floor_le hRp.le
  have hnear := Nat.lt_floor_add_one (lam^(-(2:ℝ)/13))
  have hfloor1 : (1:ℝ) ≤ ⌊lam^(-(2:ℝ)/13)⌋₊ := by
    grind
  have hRM := (Real.rpow_le_rpow_of_exponent_ge hlam
    (show lam ≤ 1 by linarith) (show -(8:ℝ)/13 ≤ -(2:ℝ)/13 by norm_num)).trans hM
  exact ⟨htwo,Nat.floor_le_of_le hRM,by linarith,hfloor⟩

end TaoTrudgianYang2025
