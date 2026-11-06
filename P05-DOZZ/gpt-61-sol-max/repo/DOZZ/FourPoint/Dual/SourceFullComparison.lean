/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.TwoRegionLaw
public import DOZZ.FourPoint.Dual.FullSpatialComparison
public import DOZZ.FourPoint.Dual.CopiedGlobalGuard
/-! Full conditional lateral comparison for the actual supplied ordinary GMC. -/
public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- Conditional comparison on the full inner and outer regions for the supplied GMC.
The global carrier, its actual radial removal identity, and its independence are constructed;
the guard inverse bound follows from the source ball moments. -/
theorem dual_source_full_lateral_comparison
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (Xc : Ω → ℂ → ℝ → ℝ) (hX : IsEquatorGFF P X) (hc : IsCircleAverage P X Xc)
    (hm : Measurable (fun p : Ω × (ℂ × ℝ) => Xc p.1 p.2.1 p.2.2))
    (hcont : ∀ᵐ ω ∂P, Continuous (fun p : ℂ × ℝ => Xc ω p.1 p.2))
    (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2) (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (α₁ α₂ α₃ : ℝ) (z : ℂ) (hz : ‖z‖ ≤ 1)
    (U₀ U₁ : Set ℂ) (hU₀ : IsOpen U₀) (hU₁ : IsOpen U₁)
    (hroot₀ : U₀ ⊆ ({0, 1} : Set ℂ)ᶜ) (hroot₁ : U₁ ⊆ ({0, 1} : Set ℂ)ᶜ)
    (A : Set ℂ) (hA : MeasurableSet A) (hU₀A : U₀ ⊆ A) (hU₁A : U₁ ⊆ Aᶜ)
    (R r η : ℝ) (hR0 : 0 ≤ R) (hR : R ≤ 1/2) (hr : 0 < r) (hη : 0 < η)
    (hn₀ : ∀ x ∈ U₀, ‖x‖ ≤ R*r) (hn₁ : ∀ x ∈ U₁, r ≤ ‖x‖)
    (hD : Metric.closedBall (3 : ℂ) (1/8) ⊆ U₁) (q : ℝ) (hq : 0 < q) :
    ∃ N : Ω → Measure ℂ, Measurable N ∧ IndepFun (originRadialPath Xc) N P ∧
      (∀ ω K, IsCompact K → K ⊆ ({0} : Set ℂ)ᶜ → N ω K < ⊤) ∧
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
  let _  := hX.1
  let Ar := originRadialPath Xc
  have hAr : AEMeasurable Ar P := originRadialPath_aemeasurable P X Xc hc hcont
  let Qr := P.map Ar
  let _ : IsProbabilityMeasure Qr := inferInstance
  obtain ⟨N, hN, hi, hfin, heq, hNa, hwhole⟩ := reflected_copied_radial_plane_observable
    P X Xc hX hc hm hcont γ hγ hγ₂ M hM
  have hguard := dual_copied_global_guard_inverse_finite P X Xc hX hc hcont γ hγ hγ₂
    M hM N hN hfin hwhole α₁ α₂ α₃ q hq.le z hz
  have hb := dual_full_spatial_comparison P X Xc hX hc hm γ α₁ α₂ α₃ z N hN hfin hNa
    Qr U₀ U₁ hU₀ hU₁ hroot₀ hroot₁ A hA hU₀A hU₁A R r η hR0 hR hr hη
      hn₀ hn₁ hD q hq hguard.ne
  have he := two_region_source_lintegral P Ar hAr γ M N hN hfin hwhole
    (fun x => ENNReal.ofReal (dualFusionKernel γ α₁ α₂ α₃ z x))
    (dual_kernel_measurable γ α₁ α₂ α₃ z).ennreal_ofReal
    U₀ U₁ hU₀.measurableSet hU₁.measurableSet
    (by grind) (by grind) (Set.disjoint_left.mpr fun x hx₀ hx₁ => hU₁A hx₁ (hU₀A hx₀)) (-q)
  dsimp only at hb ⊢
  rw [← he] at hb
  exact ⟨N, hN, hi, hfin, heq, hb⟩

end DOZZ.Proofs
