module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosPhysicalATimesAParameters
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                              

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_physical_common_shift_budget (M H : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2) :
    8*(M:ℝ)*(H:ℝ)^2*(4*(H:ℝ)+6*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)) ≤ 16*(M:ℝ)^2 := by
  pm_2290
  have hT1 : 1 ≤ T := by linarith
  pm_1668
  pm_1669
  have hHM : (H:ℝ) ≤ T^2/2 := by grind
  have hMM : T^8 ≤ (M:ℝ) := by grind
  have hQ : (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) ≤ T^3 := by
    rw [h3]
    exact Nat.floor_le (by positivity)
  pm_785
  have h23 : T^2 ≤ T^3 := by
    nlinarith [mul_le_mul_of_nonneg_right hT1 (sq_nonneg T)]
  have h7 : T^7 ≤ (M:ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hT1 (show 0 ≤ T^7 by positivity)]
  have hE : 4*(H:ℝ)+6*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) ≤ 8*T^3 := by linarith
  have hp := mul_le_mul hH2 hE
    (show 0 ≤ 4*(H:ℝ)+6*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) by positivity)
    (show 0 ≤ T^4/4 by positivity)
  have hprod : (H:ℝ)^2*(4*(H:ℝ)+6*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)) ≤ 2*(M:ℝ) := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hprod (show 0 ≤ 8*(M:ℝ) by positivity)
  nlinarith

end TaoTrudgianYang2025
