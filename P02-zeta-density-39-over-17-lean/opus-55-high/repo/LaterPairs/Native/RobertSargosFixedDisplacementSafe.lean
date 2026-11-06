module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.PrimitiveTripleSignedCount
public import LaterPairs.Native.RobertSargosConicOrientation
import WeylPort.Analytic.RealLaplace

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
open MathCollab.Density.Stronger.Atkinson MathCollab.Density.Stronger.PointMean MathCollab.Density.Stronger.Fourth

                                                                     

noncomputable section
namespace TaoTrudgianYang2025

theorem robertSargos_fixed_displacement_safe_card_le
    (S : Finset (ℤ × ℤ × ℤ)) {d q₁ q₂ : ℤ} {H Q δ : ℝ}
    (hcoeff : Int.gcd (Int.gcd d q₁ : ℤ) q₂ = 1) (hd : d ≠ 0)
    (hH : 0 < H) (hQ : 0 < Q) (hδ : 0 ≤ δ)
    (hq₁ : Q ≤ |(q₁:ℝ)|) (hsafe : 0 ≤ (q₁:ℝ)*d)
    (hh₂ : ∀ p ∈ S, (p.2.1:ℝ) ∈ Set.Icc H (2*H))
    (hprim : ∀ p ∈ S, Int.gcd (Int.gcd p.2.2 p.1 : ℤ) p.2.1 = 1)
    (hline : ∀ p ∈ S, p.2.2*d+q₁*p.1-q₂*p.2.1 = 0)
    (hnear : ∀ p ∈ S,
      |robertSargosReduced p.2.2 q₁ q₂ p.1 p.2.1 d| ≤ δ*H*Q^2) :
    (S.card:ℝ) ≤ (d.natAbs.divisors.card:ℝ)+
      8*H^2*δ/(d.natAbs:ℝ)^2*(∑ g ∈ d.natAbs.divisors, (g:ℝ)) := by
  pm_2525
  let A := (q₂:ℝ)*(q₂-d)/((q₁:ℝ)*(q₁+d))
  have hratio : ∀ p ∈ S, A-δ ≤ (p.1:ℝ)/p.2.1 ∧ (p.1:ℝ)/p.2.1 ≤ A+δ := by
    pm_2526
    have hb := robertSargos_coefficient_conic_ratio_gap hH hQ hδ
      (hh₂ p hp).1 hq₁ hsafe hl (hnear p hp)
    pm_400 δ
  pm_2527 δ
  calc
    _ ≤ (d.natAbs.divisors.card:ℝ)+
      4*H^2*((A+δ)-(A-δ))/(d.natAbs:ℝ)^2*(∑ g ∈ d.natAbs.divisors, (g:ℝ)) := hb
    _ = _ := by ring

end TaoTrudgianYang2025

