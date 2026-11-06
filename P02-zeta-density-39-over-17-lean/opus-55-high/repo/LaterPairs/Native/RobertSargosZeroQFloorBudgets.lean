module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosZeroQPolynomialBudget
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                               

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_zero_q_floor_budgets (M H : ℕ) {lam : ℝ}
    (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2) :
    0 < ⌊lam^(-(3:ℝ)/13)⌋₊ ∧ 0 < ⌊lam^(-(1:ℝ)/13)⌋₊ ∧
      (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ≤ lam^(-(1:ℝ)/13) ∧
      (H:ℝ)^2 ≤ (M:ℝ)*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)/2 ∧
      (H:ℝ)^2*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ) ≤ (M:ℝ)*(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)/2 ∧
      (H:ℝ)^2*(2*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)*lam)^((1:ℝ)/12) ≤
        (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ) := by
  pm_366
  pm_1611 hT1 T
  pm_1669
  pm_1668
  pm_899
  obtain ⟨hQ,hQlo,_⟩ := positive_floor_half_bounds hQ1
  obtain ⟨hR,_,hRhi⟩ := positive_floor_half_bounds hT1
  have hb := zero_q_physical_polynomial_budgets
    (T := T) (M := (M:ℝ)) (H := (H:ℝ))
    (Q := (⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)) (R := (⌊lam^(-(1:ℝ)/13)⌋₊:ℝ))
    hT (by rwa [h8]) (Nat.cast_nonneg H) (by rwa [h2]) (by rwa [h3])
    (Nat.cast_nonneg _) hRhi hlam hscale
  grind

end TaoTrudgianYang2025
