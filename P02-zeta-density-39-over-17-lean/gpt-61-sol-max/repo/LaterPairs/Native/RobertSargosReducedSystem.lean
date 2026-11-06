module
public import TaoTrudgianYang2025.HeathBrownExponentPairs
public import Mathlib
public import TaoTrudgianYang2025.BProcessBaseline
public import LaterPairs.Native.RobertSargosPrimitiveSystem

@[expose] public section
set_option maxHeartbeats 0


                                                                                       

noncomputable section
namespace TaoTrudgianYang2025

structure RobertSargosReducedSystem (R H Q δ : ℝ) (p : RobertSargosPoint) : Prop where
  r_ne_zero : p.r ≠ 0
  r_bound : |(p.r:ℝ)| ≤ R
  q₁_support : |(p.q₁:ℝ)| ∈ Set.Icc Q (2*Q)
  q₂_support : |(p.q₂:ℝ)| ∈ Set.Icc Q (2*Q)
  h₁_support : (p.h₁:ℝ) ∈ Set.Icc H (2*H)
  h₂_support : (p.h₂:ℝ) ∈ Set.Icc H (2*H)
  same_sign : 0 < p.q₁*p.q₂
  d_ne_zero : p.d ≠ 0
  linear : p.r*p.d+p.h₁*p.q₁-p.h₂*p.q₂ = 0
  near : |robertSargosReduced p.r p.q₁ p.q₂ p.h₁ p.h₂ p.d| ≤ δ*H*Q^2

section
variable {R H Q δ : ℝ} {p : RobertSargosPoint}
    (h : RobertSargosReducedSystem R H Q δ p)
include R H Q δ p h

theorem RobertSargosReducedSystem.to_primitive 
    (hc : Int.gcd (Int.gcd p.d p.q₁ : ℤ) p.q₂ = 1)
    (hh : Int.gcd (Int.gcd p.r p.h₁ : ℤ) p.h₂ = 1) :
    RobertSargosPrimitiveSystem R H Q δ p :=
  ⟨h.r_ne_zero,h.r_bound,h.q₁_support,h.q₂_support,h.h₁_support,
    h.h₂_support,h.same_sign,h.d_ne_zero,hc,hh,h.linear,h.near⟩

theorem RobertSargosReducedSystem.linear_real  :
    (p.r:ℝ)*p.d+(p.h₁:ℝ)*p.q₁-(p.h₂:ℝ)*p.q₂ = 0 := by
  exact_mod_cast h.linear
end



