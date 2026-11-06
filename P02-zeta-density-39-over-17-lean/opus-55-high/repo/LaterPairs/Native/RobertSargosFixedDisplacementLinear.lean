module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosFixedDisplacementSafe
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                                 

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_fixed_displacement_linear_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {d q₁ q₂ : ℤ} {R H Q δ : ℝ}
    (hcoeff : Int.gcd (Int.gcd d q₁ : ℤ) q₂ = 1) (hd : d ≠ 0)
    (hR : 0 ≤ R) (hH : 0 < H) (hQ : 0 < Q) (hδ : δ ≤ 1)
    (hq₁ : |(q₁:ℝ)| ∈ Set.Icc Q (2*Q)) (hq₂ : |(q₂:ℝ)| ∈ Set.Icc Q (2*Q))
    (hsign : 0 < q₁*q₂)
    (hh₁ : ∀ p ∈ S, (p.1:ℝ) ∈ Set.Icc H (2*H))
    (hh₂ : ∀ p ∈ S, (p.2.1:ℝ) ∈ Set.Icc H (2*H))
    (hr : ∀ p ∈ S, |(p.2.2:ℝ)| ≤ R)
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.2.2 p.1 : ℤ) p.2.1 = 1)
    (hline : ∀ p ∈ S, p.2.2*d+q₁*p.1-q₂*p.2.1 = 0)
    (hnear : ∀ p ∈ S,
      |robertSargosReduced p.2.2 q₁ q₂ p.1 p.2.1 d| ≤ δ*H*Q^2) :
    (S.card:ℝ) ≤ (d.natAbs.divisors.card:ℝ)+
      72*H*R/(d.natAbs:ℝ)^2*(∑ g ∈ d.natAbs.divisors, (g:ℝ)) := by
  pm_2525
  let A := (q₂:ℝ)/q₁
  let e := 9*R/H
  pm_61 he e
  pm_6660
  have hratio : ∀ p ∈ S, A-e ≤ (p.1:ℝ)/p.2.1 ∧ (p.1:ℝ)/p.2.1 ≤ A+e := by
    pm_2526
    have hb := robertSargos_coefficient_linear_source_gap hH hQ hδ (hr p hp)
      (hh₁ p hp) (hh₂ p hp) hq₁ hq₂ hsignR hl (hnear p hp)
    pm_400 e
  pm_2527 e
  calc
    _ ≤ (d.natAbs.divisors.card:ℝ)+
      4*H^2*((A+e)-(A-e))/(d.natAbs:ℝ)^2*(∑ g ∈ d.natAbs.divisors, (g:ℝ)) := hb
    _ = _ := by dsimp [e]; field_simp; ring

end TaoTrudgianYang2025

