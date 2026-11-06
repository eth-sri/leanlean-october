/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceParetoCutIncrement
public import DOZZ.FourPoint.Reflected.FirstOrderError
public import DOZZ.FourPoint.NormalizedLimit
import Mathlib.Tactic
/-! The fixed-cut independent-maximum source observable has its normalized Pareto limit. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual independent Pareto maximum, fixed-cut reflection mass, retained source mass and
radial restart scale give the required leading coefficient for each fixed radial buffer. -/
abbrev reflected_source_pareto_cut_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h H : ℝ) (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h)
    (hs : 2*Q γ+γ/2 < α₁+α₂+α₃) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z)  := 
  let ν := Q γ-α₁
  let a := 2*ν/γ
  let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
  let κ := γ*ν
  let c := a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p
  let C := a*p/(1-a)
  let S := (∫⁻ ω, twoSidedReflectionCutMass γ H B Z ω ^a ∂P).toReal
  let J := (∫⁻ ω, twoSidedReflectionCutMass γ H B Z ω ∂P).toReal
  let L := fun z : ℂ => (∫⁻ ω, ENNReal.ofReal
    ((reflected_radial_scale γ ν h Xc z ω)^a)*
      gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-(p+a)) ∂P).toReal
  let F := fun z : ℂ => (∫⁻ ω, ENNReal.ofReal (reflected_radial_scale γ ν h Xc z ω)*
    gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-(p+1)) ∂P).toReal
  let D := fun z : ℂ => ∫ v : Ω × Ω, (∫ w,
    (((gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+
      reflected_radial_scale γ ν h Xc z v.1*(twoSidedReflectionCutMass γ H B Z v.2).toReal*w)^(-p)-
      (gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal ^(-p)) ∂paretoMeasure 1 a) ∂P.prod P
  have hν : 0 < ν := sub_pos.mpr hα₁
  have ha : 0 < a := div_pos (mul_pos (by norm_num) hν) hγ
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have hshift : α₁+2*ν-γ/2 < Q γ := by dsimp only [ν]; linarith only [hreflect]
  have hcharge : α₁+2*ν-γ/2 = 2*Q γ-α₁-γ/2 := by dsimp only [ν]; ring
  let Λ := (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-γ/2) α₂ α₃ ^(-(p+a)) ∂P).toReal
  have hL : Tendsto (fun z : ℂ => L z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 Λ) := by
    simpa only [L,κ,a,hcharge,Λ] using reflected_leading_radial_moment_toReal_tendsto
      P X hX γ hγ hγ₂ M hM Xc hc ν α₁ α₂ α₃ ξ (p+a) h hh hξ hξ1
        (add_pos hp ha).le hshift hα₂ hα₃
  have hF : Tendsto (fun z : ℂ => F z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have ht := (isComplexLittleOAtZero_ofReal_iff (γ*(Q γ-α₁)) _).mp
      (reflected_first_order_radial_error_littleO P X hX γ hγ hγ₂ M hM Xc hc
        α₁ α₂ α₃ ξ h hh hξ hξ1 hα₁ hreflect hs)
    exact ht
  have hbound : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), |D z-c*L z*S| ≤ C*F z*J := by
    filter_upwards [eventually_punctured_zero_small] with z hz
    exact (reflected_source_pareto_cut_increment_error P X hX γ hγ hγ₂ M hM Xc hc
      α₁ α₂ α₃ ξ h p H hα₁ hreflect hα₂ hα₃ hh hp hξ hξ1 B Z hData z hz.1 hz.2.1 hz.2.2).2
  tendsto_div_of_error_bound (fun z => Real.rpow_nonneg (norm_nonneg z) κ) hL hF hbound

end DOZZ.Proofs
