module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosZeroRPolynomialBudget
public import LaterPairs.Native.ThirteenthRootScales
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                           

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_zero_r_floor_budgets
    (M H : ℕ) {lam : ℝ} (hH : 0 < H)
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2) :
    0 < ⌊lam^(-(3:ℝ)/13)⌋₊ ∧ 0 < ⌊lam^(-(1:ℝ)/13)⌋₊ ∧
      4*(H:ℝ)*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*lam ≤ 1 ∧
      (H:ℝ)^2 ≤ (M:ℝ)*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ∧
      (H:ℝ)^5*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*lam ≤ (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)^2 ∧
      (H:ℝ)^3 ≤ (M:ℝ)^2*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)^2*
        (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*lam := by
  pm_366
  have h8 : T^8 = lam^(-(8:ℝ)/13) := by
    dsimp [T]
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 8
  have h2 : T^2 = lam^(-(2:ℝ)/13) := by
    dsimp [T]
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 2
  have h3 : T^3 = lam^(-(3:ℝ)/13) := by
    dsimp [T]
    simpa only [Nat.cast_ofNat] using thirteenth_root_nat_pow hlam 3
  pm_1611 hT1 T
  pm_899
  obtain ⟨hQ,hQlo,hQhi⟩ := positive_floor_half_bounds hQ1
  obtain ⟨hR,hRlo,_⟩ := positive_floor_half_bounds hT1
  pm_7111 hM'
  pm_375 hH'
  have hQlo' : T^3/2 ≤ (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) := by rwa [h3]
  have hQhi' : (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) ≤ T^3 := by rwa [h3]
  have hb := zero_r_physical_polynomial_budgets
    (T := T) (M := (M:ℝ)) (H := (H:ℝ))
    (Q := (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)) (R := (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ))
    hT hM' (by exact_mod_cast hH) hH' hQlo' hQhi' hRlo hlam hscale
  grind

end TaoTrudgianYang2025
