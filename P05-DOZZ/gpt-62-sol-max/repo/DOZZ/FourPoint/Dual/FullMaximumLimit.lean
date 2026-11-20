/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Fusion.RetainedParetoLimit
public import DOZZ.FourPoint.Dual.LeadingRadialMoment
public import DOZZ.FourPoint.Dual.RadialFirstOrder
public import DOZZ.FourPoint.Dual.SourceMaximumPareto
public import DOZZ.Statements.Brownian.EquatorGFFLateralGMCDecomposition
public import DOZZ.FourPoint.Reflected.RestartedWilliams
import Mathlib.Tactic

/-! Leading source asymptotics for any measurable mass dominated by the reflection mass. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

theorem dual_source_maximum_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : Ω → Distr)
    (hX : IsEquatorGFF P X) (γ : ℝ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    (Xc : Ω → ℂ → ℝ → ℝ) (hc : IsCircleAverage P X Xc)
    (α₁ α₂ α₃ ξ h : ℝ) (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h)
    (hs : 2*Q γ+2/γ < α₁+α₂+α₃)
    (hshifted : 2*Q γ-α₁-2/γ < Q γ)
    (hslack : (4/γ)*(Q γ-α₁) < 2+γ*(Q γ-α₁)-γ^2/2) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z) (S : Ω → ℝ≥0∞)
    (hSm : AEMeasurable S P) (hSle : ∀ ω, S ω ≤ twoSidedReflectionMass γ B Z ω) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
    let A := fun z ω => dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ
    let b := dual_radial_scale γ ν h Xc
    Tendsto (fun z : ℂ => (∫ v : Ω × (ℝ × Ω),
      (((A z v.1).toReal + b z v.1 * (Real.exp (γ*v.2.1) * (S v.2.2).toReal))^(-p) -
        (A z v.1).toReal^(-p)) ∂P.prod ((brownianMaximumReferenceLaw ν).prod P)) / ‖z‖^((4/γ)*ν)) (𝓝[≠] (0 : ℂ))
      (𝓝 (paretoLeadingCoefficient a p *
        (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃ ^(-(p+a)) ∂P).toReal *
        (∫⁻ ω, S ω ^ a ∂P).toReal)) := by
  let ν := Q γ-α₁
  let a := 2*ν/γ
  let p := (α₁+α₂+α₃-2/γ-2*Q γ)/γ
  let κ := (4/γ)*ν
  let A (z : ℂ) (ω : Ω) := dualOuterMass γ α₁ α₂ α₃ (M ω) z ξ
  let b := dual_radial_scale γ ν h Xc
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have ha : 0 < a := by dsimp only [a, ν]; positivity
  have hβ : (-2 / γ) < Q γ := by
    simpa only [neg_div] using (neg_lt_zero.mpr (show 0 < 2/γ by positivity)).trans (by unfold Q; positivity)
  have hshift : α₁+2*ν-2/γ < Q γ := by dsimp only [ν]; linarith only [hshifted]
  have hcharge : α₁+2*ν-2/γ = 2*Q γ-α₁-2/γ := by dsimp only [ν]; ring
  have hL : Tendsto (fun z => weightedInverseMoment P (p+a) (A z)
      (fun ω => (b z ω)^a) / ‖z‖^κ) (𝓝[≠] (0 : ℂ))
      (𝓝 (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-2/γ) α₂ α₃ ^(-(p+a)) ∂P).toReal) := by
    simpa only [hcharge, weightedInverseMoment, A, b, a, κ] using dual_leading_radial_moment_toReal_tendsto P X hX γ hγ hγ₂ M hM Xc hc
      ν α₁ α₂ α₃ ξ (p+a) h hh hξ hξ1 (add_pos hp ha).le hshift hα₂ hα₃
  have hF : Tendsto (fun z => weightedInverseMoment P (p+1) (A z) (b z) / ‖z‖^κ)
      (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    have ht := dual_radial_first_order_littleO P X hX γ hγ hγ₂ M hM Xc hc
      α₁ α₂ α₃ ξ (p+1) h κ hh hξ hξ1 (by positivity) hslack
    apply ht.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [weightedInverseMoment, b, dual_radial_scale_eq_restart γ ν h Xc z hz]
    rfl
  have ht := fusion_retained_pareto_increment_tendsto P X hX γ hγ hγ₂ M hM Xc hc
    (-2 / γ) 2 α₁ α₂ α₃ ξ h p κ _ hβ hα₁ hreflect hα₂ hα₃ hh hp hξ hξ1 B Z hData S hSm hSle hL hF
  apply ht.congr'
  let _ : IsProbabilityMeasure P := hX.1
  obtain ⟨Ar, _, hAr, _, hB, _, _, _, _, _⟩ := DOZZ.equatorGFF_lateral_GMC_decomposition P X M γ hγ hγ₂ hX hM
  let W := P.map (fun ω => radialPositiveHalf (Ar ω))
  have hW := radialPositiveHalf_map_isBrownian P Ar hAr hB
  filter_upwards [eventually_punctured_unitBall] with z ⟨hz₀, hz₁, hzn⟩
  have hInt := (fusion_retained_pareto_increment_error P X hX γ hγ hγ₂ M hM Xc hc
    (-2 / γ) 2 α₁ α₂ α₃ ξ h p hβ hα₁ hreflect hα₂ hα₃ hh hp hξ hξ1
    B Z hData S hSm hSle z hz₀ hz₁ hzn.le).1
  have he := dual_source_fixed_maximum_increment_eq_pareto P X hX γ hγ hγ₂ M hM Xc hc
    α₁ α₂ α₃ ξ h p hα₁ hα₂ hα₃ hh hp hξ hξ1
    (fun ω => (S ω).toReal) hSm.ennreal_toReal (ae_of_all _ (fun _ => ENNReal.toReal_nonneg))
    W hW z hz₀ hz₁ hzn.le hInt
  exact congrArg (· / ‖z‖^κ) he.symm

end DOZZ.Proofs
