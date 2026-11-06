module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosZeroQFloorBudgets
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                               

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_physical_a_times_a_ranges (M H : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M)
    (hHmin : lam^(-(1:ℝ)/7) ≤ H) (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2) :
    0 < H ∧ 0 < ⌊lam^(-(3:ℝ)/13)⌋₊ ∧ 0 < ⌊lam^(-(1:ℝ)/13)⌋₊ ∧
      ⌊lam^(-(3:ℝ)/13)⌋₊ ≤ M ∧ ⌊lam^(-(1:ℝ)/13)⌋₊ ≤ 2*H := by
  obtain ⟨hQ,hR,hRhi,_⟩ := robertSargos_zero_q_floor_budgets M H hlam hsmall hM hHmax
  have hlam1 : lam ≤ 1 := by linarith
  have hH : 0 < H := by
    have hc := (Real.rpow_pos_of_pos hlam (-(1:ℝ)/7)).trans_le hHmin
    exact_mod_cast hc
  have hQM : (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) ≤ M :=
    (Nat.floor_le (Real.rpow_nonneg hlam.le _)).trans
      ((Real.rpow_le_rpow_of_exponent_ge hlam hlam1
        (by norm_num : -(8:ℝ)/13 ≤ -3/13)).trans hM)
  have hRH : (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ≤ H :=
    hRhi.trans ((Real.rpow_le_rpow_of_exponent_ge hlam hlam1
      (by norm_num : -(1:ℝ)/7 ≤ -1/13)).trans hHmin)
  exact ⟨hH,hQ,hR,by exact_mod_cast hQM,by exact_mod_cast (show
    (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ≤ 2*(H:ℝ) by linarith [Nat.cast_nonneg (α := ℝ) H])⟩

theorem robertSargos_physical_endpoint_budget (M H : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2) :
    16*(M:ℝ)*(H:ℝ)^2*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ≤ 4*(M:ℝ)^2 := by
  pm_2290
  have hT1 : 1 ≤ T := by linarith
  pm_291
  pm_1669
  pm_375 hHM
  pm_7111 hMM
  have hR : (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ≤ T := Nat.floor_le (by positivity)
  pm_785
  have h5 : T^5 ≤ (M:ℝ) := by
    pm_7304 h3 T hT1
    nlinarith [mul_le_mul_of_nonneg_left h3 (show 0 ≤ T^5 by positivity)]
  have hprod := mul_le_mul hH2 hR (Nat.cast_nonneg _) (show 0 ≤ T^4/4 by positivity)
  have hHR : (H:ℝ)^2*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ≤ (M:ℝ)/4 := by nlinarith
  have he := mul_le_mul_of_nonneg_left hHR (show 0 ≤ 16*(M:ℝ) by positivity)
  nlinarith

end TaoTrudgianYang2025
