/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.RetainedParetoLimit
public import DOZZ.FourPoint.Reflected.FirstOrderError
public import DOZZ.FourPoint.Reflected.LeadingRadialMoment
import Mathlib.Tactic

/-! Leading source asymptotics for any measurable mass dominated by the reflection mass. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

theorem reflected_source_pareto_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h : ℝ) (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h)
    (hs : 2*Q γ+γ/2 < α₁+α₂+α₃) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z) (S : Ω → ℝ≥0∞)
    (hSm : AEMeasurable S P) (hSle : ∀ ω, S ω ≤ twoSidedReflectionMass γ B Z ω) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
    let A := fun z ω => gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ
    let b := reflected_radial_scale γ ν h Xc
    Tendsto (fun z : ℂ => (∫ v, paretoMassIncrement a p (A z) S (b z) v ∂P.prod P) / ‖z‖^(γ*ν)) (𝓝[≠] (0 : ℂ))
      (𝓝 (paretoLeadingCoefficient a p *
        (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-γ/2) α₂ α₃ ^(-(p+a)) ∂P).toReal *
        (∫⁻ ω, S ω ^ a ∂P).toReal)) := by
  let ν := Q γ-α₁
  let a := 2*ν/γ
  let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
  let κ := γ*ν
  let A (z : ℂ) (ω : Ω) := gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let b := reflected_radial_scale γ ν h Xc
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have ha : 0 < a := by dsimp only [a, ν]; positivity
  have hβ : (-γ / 2) < Q γ := by
    simpa only [neg_div] using (neg_lt_zero.mpr (show 0 < γ/2 by positivity)).trans (by unfold Q; positivity)
  have hshift : α₁+2*ν-γ/2 < Q γ := by dsimp only [ν]; linarith only [hreflect]
  have hcharge : α₁+2*ν-γ/2 = 2*Q γ-α₁-γ/2 := by dsimp only [ν]; ring
  have hL : Tendsto (fun z => weightedInverseMoment P (p+a) (A z)
      (fun ω => (b z ω)^a) / ‖z‖^κ) (𝓝[≠] (0 : ℂ))
      (𝓝 (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-γ/2) α₂ α₃ ^(-(p+a)) ∂P).toReal) := by
    simpa only [hcharge, weightedInverseMoment, A, b, a, κ] using reflected_leading_radial_moment_toReal_tendsto P X hX γ hγ hγ₂ M hM Xc hc
      ν α₁ α₂ α₃ ξ (p+a) h hh hξ hξ1 (add_pos hp ha).le hshift hα₂ hα₃
  exact fusion_retained_pareto_increment_tendsto P X hX γ hγ hγ₂ M hM Xc hc
    (-γ / 2) (γ ^ 2 / 2) α₁ α₂ α₃ ξ h p κ _ hβ hα₁ hreflect hα₂ hα₃ hh hp hξ hξ1 B Z hData S hSm hSle hL (by
    exact (isComplexLittleOAtZero_ofReal_iff κ _).mp (reflected_first_order_radial_error_littleO
      P X hX γ hγ hγ₂ M hM Xc hc α₁ α₂ α₃ ξ h hh hξ hξ1 hα₁ hreflect hs))

end DOZZ.Proofs
