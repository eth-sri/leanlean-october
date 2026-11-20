/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.FullSpatialComparison
import DOZZ.FourPoint.Dual.SpatialKernel
public import DOZZ.FourPoint.Dual.SpatialGuard
import DOZZ.FourPoint.Reflected.DecorrelationCarrier
public import DOZZ.GFFStructure.ContinuousCircleAverage
public import DOZZ.MeasureTheory.FiniteOnChart
/-! Full conditional lateral comparison for the actual supplied ordinary GMC. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Conditional comparison on the full inner and outer regions for the supplied GMC.
The global carrier, its actual radial removal identity, and its independence are constructed;
the guard inverse bound follows from the source ball moments. -/
theorem dual_source_full_lateral_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hcircle : IsContinuousCircleAverage P X Xc)
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (U₀ U₁ : Set ℂ) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hroot₀ : U₀ ⊆ ({0, 1} : Set ℂ)ᶜ) (hroot₁ : U₁ ⊆ ({0, 1} : Set ℂ)ᶜ)
    (A : Set ℂ) (hA : MeasurableSet A) (hU₀A : U₀ ⊆ A) (hU₁A : U₁ ⊆ Aᶜ)
    (R r η : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1/2) (hr : 0 < r) (hη : 0 < η)
    (hn₀ : ∀ x ∈ U₀, ‖x‖ ≤ R*r) (hn₁ : ∀ x ∈ U₁, r ≤ ‖x‖)
    (hD : Metric.closedBall (3 : ℂ) (1/8) ⊆ U₁) (q : ℝ) (hq : 0 < q) :
    ∃ N : Ω → Measure ℂ, Measurable N ∧ IndepFun (originRadialPath Xc) N P ∧
      (∀ ω, FiniteOnChart ({0} : Set ℂ)ᶜ (N ω)) ∧
      N =ᵐ[P] (fun ω => (M ω).withDensity
        (lateralRadialWeight γ (originRadialPath Xc ω))) ∧
      let J := fun (U : Set ℂ) (p : TwoSidedPath × Ω) => ∫⁻ x in U,
        ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x)*
          ENNReal.ofReal (reflected_global_reinsertionWeight γ p.1 x) ∂N p.2
      let original := ∫⁻ ω,
        ((∫⁻ x in U₀, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω)+
         (∫⁻ x in U₁, ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x) ∂M ω))^(-q) ∂P
      let copied := ∫⁻ p : TwoSidedPath × (Ω × Ω),
        (J U₀ (p.1, p.2.1)+J U₁ (p.1, p.2.2))^(-q) ∂(P.map (originRadialPath Xc)).prod (P.prod P)
      let m := ENNReal.ofReal (Real.exp (γ^2*(2*R+η)/2*(q^2+q)))
      original ≤ m*copied ∧ copied ≤ m*original := by
  obtain ⟨N, hN, hi, hfin, heq, hNa, hwhole⟩ := reflected_copied_radial_plane_observable
    P X Xc hX hcircle γ hγ hγ₂ M hM
  exact ⟨N, hN, hi, hfin, heq, source_full_lateral_comparison_on_carrier
    P X Xc hX hcircle γ M (dualFusionKernel γ α₁ α₂ α₃ z)
    (dual_kernel_measurable γ α₁ α₂ α₃ z) (dual_kernel_nonneg γ α₁ α₂ α₃ z)
    (dual_kernel_continuousOn γ α₁ α₂ α₃ z) N hN hfin hwhole hNa
    U₀ U₁ hU₀ hU₁ hroot₀ hroot₁ A hA hU₀A hU₁A R r η hR0 hR hr hη hn₀ hn₁ hD q hq
    (dual_spatial_guard_inverse_finite P X hX γ hγ hγ₂ M hM α₁ α₂ α₃ q hq.le z hz)⟩

end DOZZ.Proofs
