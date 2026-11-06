/-
Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import DOZZ.FourPoint.Reflected.SourceParetoIncrement
public import DOZZ.FourPoint.Reflected.FirstOrderError
import Mathlib.Tactic
/-! The full independent-maximum source observable has its normalized Pareto limit. -/
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
namespace DOZZ.Proofs

/-- The actual independent Pareto maximum, full reflection mass, retained source mass and
radial restart scale give the required leading coefficient for each fixed radial buffer. -/
theorem reflected_source_pareto_increment_tendsto
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) X
    (hX : IsEquatorGFF P X) γ (hγ : 0 < γ) (hγ₂ : γ < 2)
    (M : Ω → Measure ℂ) (hM : IsGMCOf P X γ M)
    Xc (hc : IsCircleAverage P X Xc)
    α₁ α₂ α₃ ξ h (hα₁ : α₁ < Q γ) (hreflect : Q γ-α₁ < γ/2)
    (hα₂ : α₂ < Q γ) (hα₃ : α₃ < Q γ) (hh : 0 ≤ h)
    (hs : 2*Q γ+γ/2 < α₁+α₂+α₃) (hξ : 0 < ξ) (hξ1 : ξ < 1)
    (B : Ω → BrownianPath × BrownianPath) (Z : Ω → Measure ℝ)
    (hData : IsReflectionData P γ α₁ B Z) :
    let ν := Q γ-α₁
    let a := 2*ν/γ
    let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
    Tendsto (fun z => (fun z => ∫ v : Ω × Ω, (∫ w, (((gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+ reflected_radial_scale γ ν h Xc z v.1*(twoSidedReflectionMass γ B Z v.2).toReal*w)^(-p)- (gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal ^(-p)) ∂paretoMeasure 1 a) ∂P.prod P) z/‖z‖^(γ*ν)) (𝓝[≠] (0 : ℂ))
      (𝓝 ((a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p)*
        (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-γ/2) α₂ α₃ ^(-(p+a)) ∂P).toReal*
        (∫⁻ ω, twoSidedReflectionMass γ B Z ω ^a ∂P).toReal)) := by
  let ν := Q γ-α₁
  let a := 2*ν/γ
  let p := (α₁+α₂+α₃-γ/2-2*Q γ)/γ
  let κ := γ*ν
  let c := a*Real.Gamma (-a)*Real.Gamma (p+a)/Real.Gamma p
  let S := (∫⁻ ω, twoSidedReflectionMass γ B Z ω ^a ∂P).toReal
  let L := fun z => (∫⁻ ω, ENNReal.ofReal
    ((reflected_radial_scale γ ν h Xc z ω)^a)*
      gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-(p+a)) ∂P).toReal
  let D := fun z => ∫ v : Ω × Ω, (∫ w,
    (((gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal+
      reflected_radial_scale γ ν h Xc z v.1*(twoSidedReflectionMass γ B Z v.2).toReal*w)^(-p)-
      (gammaHalfOuterMass γ α₁ α₂ α₃ (M v.1) z ξ).toReal ^(-p)) ∂paretoMeasure 1 a) ∂P.prod P
  have hp : 0 < p := div_pos (by linarith only [hs]) hγ
  let Λ := (∫⁻ ω, rho γ (M ω) (2*Q γ-α₁-γ/2) α₂ α₃ ^(-(p+a)) ∂P).toReal
  have herr : Tendsto (fun z => (D z-c*L z*S)/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall fun z => norm_nonneg _) ?_ (by simpa only [mul_zero] using (show Tendsto (fun z : ℂ => (fun z : ℂ => (∫⁻ ω, ENNReal.ofReal (reflected_radial_scale γ ν h Xc z ω)* gammaHalfOuterMass γ α₁ α₂ α₃ (M ω) z ξ ^(-(p+1)) ∂P).toReal) z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 0) by exact ((isComplexLittleOAtZero_ofReal_iff (γ*(Q γ-α₁)) _).mp (reflected_first_order_radial_error_littleO P X hX γ hγ hγ₂ M hM Xc hc α₁ α₂ α₃ ξ h hh hξ hξ1 hα₁ hreflect hs))).const_mul ((a*p/(1-a))*((∫⁻ ω, twoSidedReflectionMass γ B Z ω ∂P).toReal)))
    filter_upwards [(by filter_upwards [(show ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), z ≠ 0 ∧ z ≠ 1 ∧ ‖z‖ ≤ 1 by filter_upwards [self_mem_nhdsWithin, ((continuous_norm.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num : ‖(0 : ℂ)‖ < 1))] with z hz hzn; exact ⟨hz,(by intro he; simp [he] at hzn),hzn.le⟩)] with z hz; exact (reflected_source_pareto_increment_error P X hX γ hγ hγ₂ M hM Xc hc α₁ α₂ α₃ ξ h p hα₁ hreflect hα₂ hα₃ hh hp hξ hξ1 B Z hData z hz.1 hz.2.1 hz.2.2).2)] with z hz
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
    convert (div_le_div_of_nonneg_right hz (Real.rpow_nonneg (norm_nonneg z) κ)) using 1; ring
  change Tendsto (fun z : ℂ => D z / ‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 (c*Λ*S))
  simpa only [Pi.add_apply, zero_add, (show (fun z => (D z-c*L z*S)/‖z‖^κ+c*(L z/‖z‖^κ)*S) = (fun z => D z/‖z‖^κ) by funext z; ring)] using (herr.add (((show Tendsto (fun z : ℂ => L z/‖z‖^κ) (𝓝[≠] (0 : ℂ)) (𝓝 Λ) by simpa only [L,κ,a,(show α₁+2*ν-γ/2 = 2*Q γ-α₁-γ/2 by dsimp only [ν]; ring),Λ] using reflected_leading_radial_moment_toReal_tendsto P X hX γ hγ hγ₂ M hM Xc hc ν α₁ α₂ α₃ ξ (p+a) h hh hξ hξ1 (add_pos hp (div_pos (mul_pos (by norm_num) (sub_pos.mpr hα₁)) hγ)).le (by dsimp only [ν]; linarith only [hreflect]) hα₂ hα₃).const_mul c).mul_const S))

end DOZZ.Proofs
