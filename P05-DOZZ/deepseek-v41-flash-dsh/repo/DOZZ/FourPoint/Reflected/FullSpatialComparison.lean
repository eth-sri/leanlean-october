/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.SharedHyp
public import DOZZ.FourPoint.FullSpatialComparisonGeneric
public import DOZZ.FourPoint.Reflected.GlobalCompactMassComparison
/-! The compact conditional comparison extends to full separated spatial regions. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_full_spatial_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : MeasurableCircleAvg Xc)
    (γ α₁ α₂ α₃ : ℝ) (z : ℂ) (N : Ω → Measure ℂ) (hNm : Measurable N)
    (hfin : FiniteOffOrigin N)
    (hNa : ∀ ρ : ℝ, 0 < ρ → IsAdmissibleGMCVersion P (originLateralChart ρ)
      originLateralPlaneDensity (originLateralCircleRegularization Xc ρ) γ
      (fun ω => (N ω).restrict (originLateralChart ρ)))
    (Q : Measure TwoSidedPath) [IsProbabilityMeasure Q]
    (U₀ U₁ : Set ℂ) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hroot₀ : U₀ ⊆ ({0, 1} : Set ℂ)ᶜ) (hroot₁ : U₁ ⊆ ({0, 1} : Set ℂ)ᶜ)
    (A : Set ℂ) (hA : MeasurableSet A) (hU₀A : U₀ ⊆ A) (hU₁A : U₁ ⊆ Aᶜ)
    (R r η : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1/2) (hr : 0 < r) (hη : 0 < η)
    (hn₀ : ∀ x ∈ U₀, ‖x‖ ≤ R*r) (hn₁ : ∀ x ∈ U₁, r ≤ ‖x‖)
    (hD : Metric.closedBall (3 : ℂ) (1/8) ⊆ U₁) (q : ℝ) (hq : 0 < q)
    (hguard : (∫⁻ a, ∫⁻ ω, (∫⁻ x in Metric.closedBall (3 : ℂ) (1/8),
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ a x) ∂N ω)^(-q) ∂P ∂Q) ≠ ⊤) :
    let J := fun (U : Set ℂ) (p : TwoSidedPath × Ω) => ∫⁻ x in U,
      ENNReal.ofReal (gammaHalfKernel γ α₁ α₂ α₃ z x)*
        ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2
    let m := ENNReal.ofReal (Real.exp (γ^2*(2*R+η)/2*(q^2+q)))
    (∫⁻ p, (J U₀ p+J U₁ p)^(-q) ∂Q.prod P) ≤
      m*(∫⁻ p : TwoSidedPath × (Ω × Ω),
        (J U₀ (p.1, p.2.1)+J U₁ (p.1, p.2.2))^(-q) ∂Q.prod (P.prod P)) ∧
    (∫⁻ p : TwoSidedPath × (Ω × Ω),
        (J U₀ (p.1, p.2.1)+J U₁ (p.1, p.2.2))^(-q) ∂Q.prod (P.prod P)) ≤
      m*(∫⁻ p, (J U₀ p+J U₁ p)^(-q) ∂Q.prod P) := full_spatial_comparison_generic P X Xc hX hc hm (gammaHalfKernel γ α₁ α₂ α₃ z)
    (reflected_gammaHalfKernel_measurable γ α₁ α₂ α₃ z) (gammaHalfKernel_nonneg γ α₁ α₂ α₃ z)
    γ N hNm hfin hNa Q U₀ U₁ hU₀ hU₁ hroot₀ hroot₁
    ((reflected_spatial_kernel_continuousOn γ α₁ α₂ α₃ z).mono hroot₀) ((reflected_spatial_kernel_continuousOn γ α₁ α₂ α₃ z).mono hroot₁)
    A hA hU₀A hU₁A R r η hR0 hR hr hη hn₀ hn₁ hD q hq hguard

end DOZZ.Proofs
