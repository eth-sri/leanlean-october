/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceWilliamsSqueeze
public import DOZZ.FourPoint.Reflected.SourceWilliamsParetoIntegral
public import DOZZ.FourPoint.Reflected.SourceParetoLimit
public import DOZZ.FourPoint.Reflected.SourceParetoCutLimit
public import DOZZ.FourPoint.Reflected.CutMoment
public import DOZZ.FourPoint.Reflected.OrderedCutSqueeze
import Mathlib.Tactic
/-! Ordered removal of the maximum cutoff in the actual source Williams expectation. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
namespace DOZZ.Proofs

/-- The actual variable-last-cut Williams increment has the reflected source coefficient.
The maximum cutoff is removed after the punctured spatial limit, with no uniform cutoff-error
assumption. -/
theorem reflected_source_williams_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    Xc (hc : IsCircleAverage P X Xc)
    α₁ α₂ α₃ ξ h (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h)
    (hs : 2*Q γ+γ/2 < α₁+α₂+α₃) (hξ : 0 < ξ) (hξ₁ : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z)
    (B₀ : Measure BrownianPath) [SFinite B₀] (hB₀ : IsBrownianReal (fun t p => p t) B₀) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
    Tendsto (fun z => (fun z => ∫ v : Ω × (ℝ × Ω), ((gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+ reflected_radial_scale γ ν h Xc z v.1*Real.exp (γ*v.2.1)* (twoSidedReflectionCutMass γ v.2.1 B Z v.2.2).toReal)^(-p)- (gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal^(-p) ∂P.prod ((brownianMaximumReferenceLaw ν).prod P)) z/‖z‖^(γ*ν)) (𝓝[≠] (0 : ℂ))
      (𝓝 ((a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-γ/2) α₂ α₃ ^(-(p+a)) ∂P).toReal*
          reflectionBarR P γ α₁ B Z)) := by
  let _ : IsProbabilityMeasure P := hX.1
  let ν := Q γ-α₁
  let a := 2*ν/γ
  let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
  let κ := γ*ν
  let c := a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p
  let Λ := (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-γ/2) α₂ α₃ ^(-(p+a)) ∂P).toReal
  let A := fun z ω => (gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ).toReal
  let b := fun z => reflected_radial_scale γ ν h Xc z
  let μ := brownianMaximumReferenceLaw ν
  let W := fun z => ∫ v : Ω × (ℝ × Ω),
    (A z v.1+b z v.1*Real.exp (γ*v.2.1)*
      (twoSidedReflectionCutMass γ v.2.1 B Z v.2.2).toReal)^(-p)-(A z v.1)^(-p) ∂P.prod (μ.prod P)
  let G := fun z => ∫ v : Ω × Ω, (∫ w,
    (A z v.1+b z v.1*(twoSidedReflectionMass γ B Z v.2).toReal*w)^(-p)-(A z v.1)^(-p)
      ∂paretoMeasure 1 a) ∂P.prod P
  let K := fun H => fun z => ∫ v : Ω × Ω, (∫ w,
    (A z v.1+b z v.1*(twoSidedReflectionCutMass γ H B Z v.2).toReal*w)^(-p)-(A z v.1)^(-p)
      ∂paretoMeasure 1 a) ∂P.prod P
  let F := fun z => (∫⁻ ω, ENNReal.ofReal (b z ω)*
    gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-(p+1)) ∂P).toReal
  let J := (∫⁻ ω, twoSidedReflectionMass γ B Z ω ∂P).toReal
  let E := fun H z => p*Real.exp (γ*H)*F z*J
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  have hBm := conditionedPair_aemeasurable P B ν hData.1
  have hKm (H : ℝ) := (twoSidedReflectionCutMass_aemeasurable P γ H B Z hBm
    hData.2.1.2.2.2.1 hData.2.1.2.2.2.2.1).ennreal_toReal
  have hsand H (hH : 0 < H) : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ),
      G z ≤ W z ∧ W z ≤ K H z+E H z := by
    filter_upwards [(show ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 ∧ z ≠ 1 ∧ ‖z‖ ≤ 1 by filter_upwards [self_mem_nhdsWithin,((continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1))] with z hz hzn; exact ⟨hz,(by intro he; simp [he] at hzn),hzn.le⟩)] with z hz
    have hbnd := (reflected_source_williams_expectation_squeeze P X hX γ hγ hγ₂ M hM Xc hc
      α₁ α₂ α₃ ξ h p hα₁ hα₂ hα₃ hh hp hξ hξ₁ B Z hData B₀ hB₀
        (Real.toNNReal H) (by simpa only [Real.coe_toNNReal H hH.le] using hH)
        z hz.1 hz.2.1 hz.2.2).2
    simp only [Real.coe_toNNReal H hH.le] at hbnd
    rw [(reflected_source_williams_pareto_integral P X hX γ hγ hγ₂ M hM Xc hc α₁ α₂ α₃ ξ h p hα₁ hα₂ hα₃ hh hp hξ hξ₁ B₀ hB₀ (fun ω => (twoSidedReflectionMass γ B Z ω).toReal) (ae_of_all P fun _ => ENNReal.toReal_nonneg) ((twoSidedReflectionMass_aemeasurable_of_lateral P γ B Z hBm hData.2.1).ennreal_toReal) z hz.1 hz.2.1 hz.2.2),(reflected_source_williams_pareto_integral P X hX γ hγ hγ₂ M hM Xc hc α₁ α₂ α₃ ξ h p hα₁ hα₂ hα₃ hh hp hξ hξ₁ B₀ hB₀ (fun ω => (twoSidedReflectionCutMass γ H B Z ω).toReal) (ae_of_all P fun _ => ENNReal.toReal_nonneg) (hKm H) z hz.1 hz.2.1 hz.2.2)] at hbnd
    exact hbnd
  have hF : Tendsto (fun z => F z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 0) :=
    (isComplexLittleOAtZero_ofReal_iff (γ*(Q γ-α₁)) _).mp
      (reflected_first_order_radial_error_littleO P X hX γ hγ hγ₂ M hM Xc hc
        α₁ α₂ α₃ ξ h hh hξ hξ₁ hα₁ hreflect hs)
  have hE H : Tendsto (fun z => E H z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    convert (hF.const_mul (p*Real.exp (γ*H)*J)) using 1
    · funext z; dsimp only [E]; ring
    · rw [mul_zero]
  change Tendsto (fun z : ℂ => W z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 (c*Λ*reflectionBarR P γ α₁ B Z))
  apply reflected_ordered_cut_squeeze _ _ (fun z => G z/‖z‖^κ)
    (fun H z => K H z/‖z‖^κ) (fun H z => E H z/‖z‖^κ) _ (fun H => c*Λ*(∫⁻ ω, twoSidedReflectionCutMass γ H B Z ω ^a ∂P).toReal)
    (reflected_source_pareto_increment_tendsto P X hX γ hγ hγ₂ M hM Xc hc α₁ α₂ α₃ ξ h hα₁ hreflect hα₂ hα₃ hh hs hξ hξ₁ B Z hData) (fun H _ => (fun H => reflected_source_pareto_cut_increment_tendsto P X hX γ hγ hγ₂ M hM Xc hc α₁ α₂ α₃ ξ h H hα₁ hreflect hα₂ hα₃ hh hs hξ hξ₁ B Z hData) H) (fun H _ => hE H) ((reflected_cut_moment_tendsto P γ α₁ B Z hγ hγ₂ hα₁ hreflect hData).const_mul (c*Λ))
  · filter_upwards [hsand 1 zero_lt_one] with z hz
    exact div_le_div_of_nonneg_right hz.1 (Real.rpow_nonneg (norm_nonneg z) κ)
  · intro H hH
    filter_upwards [hsand H hH] with z hz
    simpa only [add_div] using (div_le_div_of_nonneg_right hz.2 (Real.rpow_nonneg (norm_nonneg z) κ))

end DOZZ.Proofs
