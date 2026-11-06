module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosCoefficientGeometry
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                    
                                                                               

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargosReduced_swap {r q₁ q₂ h₁ h₂ d : ℝ}
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0) :
    robertSargosReduced r q₂ q₁ h₂ h₁ (-d) =
      -robertSargosReduced r q₁ q₂ h₁ h₂ d := by
  dsimp [robertSargosReduced]
  grind

theorem robertSargos_safe_pivot {q₁ q₂ d : ℝ} (hsign : 0 < q₁*q₂) :
    0 ≤ q₁*d ∨ 0 ≤ q₂*(-d) := by
  by_cases h : 0 ≤ q₁*d
  grind
  right
  have hn : q₁*d < 0 := lt_of_not_ge h
  rcases mul_pos_iff.mp hsign with hp | hm
  · have hd : d ≤ 0 := by nlinarith [hp.1]
    exact mul_nonneg hp.2.le (neg_nonneg.mpr hd)
  · have hd : 0 ≤ d := by nlinarith [hm.1]
    exact mul_nonneg_of_nonpos_of_nonpos hm.2.le (neg_nonpos.mpr hd)

theorem robertSargos_coefficient_linear_source_gap {r q₁ q₂ h₁ h₂ d R H Q δ : ℝ}
    (hH : 0 < H) (hQ : 0 < Q) (hδ : δ ≤ 1) (hr : |r| ≤ R)
    (hh₁ : h₁ ∈ Set.Icc H (2*H)) (hh₂ : h₂ ∈ Set.Icc H (2*H))
    (hq₁ : |q₁| ∈ Set.Icc Q (2*Q)) (hq₂ : |q₂| ∈ Set.Icc Q (2*Q))
    (hsign : 0 < q₁*q₂)
    (hlin : r*d+h₁*q₁-h₂*q₂ = 0)
    (hnear : |robertSargosReduced r q₁ q₂ h₁ h₂ d| ≤ δ*H*Q^2) :
    |h₁/h₂-q₂/q₁| ≤ 9*R/H := by
  pm_1003
  have hb := robertSargos_coefficient_linear_ratio_gap hH hQ hr hd hh₂.1 hq₁.1 hlin
  calc
    _ ≤ R*(9*Q)/(H*Q) := hb
    _ = _ := by field_simp

end TaoTrudgianYang2025

